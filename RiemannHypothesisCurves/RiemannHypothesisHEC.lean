import Mathlib
import RiemannHypothesisCurves.StepanovPolynomial

noncomputable def hyperellipticCurve (F : Type*) [Field F] (f : Polynomial F) : Set (F × F) :=
  {p | p.2 ^ 2 = Polynomial.eval p.1 f}

lemma hasse_vanishing_card_bound
  (F : Type*) [Field F] [DecidableEq F]
  (r : Polynomial F) (ℓ : ℕ)
  (S : Finset F)
  (hr : r ≠ 0)
  (hℓ_pos : 0 < ℓ)
  (hvan : ∀ x ∈ S, ∀ k < ℓ, (hasseDerivOp F k r).eval x = 0) :
  (S.card : ℝ) ≤ (r.natDegree : ℝ) / ℓ :=
by
  let s : F → Polynomial F := fun x => (Polynomial.X - Polynomial.C x) ^ ℓ
  have hpair_all : Pairwise fun x y : F => IsCoprime (s x) (s y) := by
    have hlin :
        Pairwise fun x y : F =>
          IsCoprime (Polynomial.X - Polynomial.C x)
            (Polynomial.X - Polynomial.C y) := by
      simpa [Function.onFun] using
        (Polynomial.pairwise_coprime_X_sub_C (K := F)
          (s := fun x : F => x) (H := fun {x} {y} h => h))
    exact hlin.mono fun x y hcop => by
      simpa [s] using (IsCoprime.pow hcop : _)
  have hprod_dvd : (∏ x ∈ S, s x) ∣ r := by
    refine
      Finset.prod_dvd_of_coprime (t := S) (s := s) (z := r) ?_ ?_
    · intro x hx y hy hxy
      simpa [Function.onFun] using hpair_all hxy
    · intro x hx
      simpa [s] using
        hasse_divisibility (F := F) (f := r) (a := x) (ℓ := ℓ) (hvan x hx)
  have hP_nat_eq :
      ((∏ x ∈ S, s x : Polynomial F).natDegree) = S.card * ℓ := by
    calc
      ((∏ x ∈ S, s x : Polynomial F).natDegree)
          = ∑ x ∈ S, (s x).natDegree := by
              simpa using
                (Polynomial.natDegree_prod_of_monic (s := S) (f := s)
                  (by
                    intro x hx
                    simpa [s] using (Polynomial.monic_X_sub_C x).pow ℓ))
      _ = ∑ x ∈ S, ℓ := by
            simp [s]
      _ = S.card * ℓ := by simp
  have h_nat' : S.card * ℓ ≤ r.natDegree := by
    have hnat_le :
        ((∏ x ∈ S, s x : Polynomial F).natDegree) ≤ r.natDegree :=
      (Polynomial.natDegree_le_iff_degree_le).2
        ((Polynomial.degree_le_of_dvd
            (p := ∏ x ∈ S, s x) (q := r) hprod_dvd hr).trans
          (Polynomial.degree_le_natDegree (p := r)))
    simpa [hP_nat_eq] using hnat_le
  have hℓ_pos' : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
  have h_real_mul : (S.card : ℝ) * (ℓ : ℝ) ≤ (r.natDegree : ℝ) := by
    exact_mod_cast h_nat'
  have hne : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ_pos'
  simpa [mul_comm, mul_left_comm, mul_assoc, hne, div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right h_real_mul (inv_nonneg.mpr hℓ_pos'.le))

lemma ceil_sqrt_le_div_three
  (q : ℕ) (hq : 15 ≤ q) :
  Nat.ceil (Real.sqrt q) ≤ q / 3 :=
by
  set k : ℕ := q / 3 with hk
  have hk_ge5 : 5 ≤ k := by
    have : 5 * 3 ≤ q := by simpa using hq
    simpa [hk] using (Nat.le_div_iff_mul_le (by decide : 0 < 3)).2 this
  have hq_le_2plus3k : q ≤ 2 + 3 * k := by
    have hmod : q % 3 ≤ 2 :=
      Nat.lt_succ_iff.mp (Nat.mod_lt q (by decide : 0 < 3))
    have h : q % 3 + k * 3 ≤ 2 + k * 3 := Nat.add_le_add_right hmod _
    simpa [hk, Nat.mod_add_div, Nat.mul_comm] using h
  have h2plus3k_le_kk : 2 + 3 * k ≤ k * k := by
    have h2_le_k : 2 ≤ k := (by decide : 2 ≤ 5).trans hk_ge5
    have h4_le_k : 4 ≤ k := (by decide : 4 ≤ 5).trans hk_ge5
    calc
      2 + 3 * k ≤ k + 3 * k := Nat.add_le_add_right h2_le_k _
      _ = 4 * k := by ring_nf
      _ ≤ k * k := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left k h4_le_k
  have h_sqrt_le : Real.sqrt (q : ℝ) ≤ k := by
    refine (Real.sqrt_le_iff).2 ?_
    refine ⟨?_, ?_⟩
    · exact_mod_cast (Nat.zero_le k)
    · have : (q : ℝ) ≤ (k : ℝ) * k := by
        exact_mod_cast (hq_le_2plus3k.trans h2plus3k_le_kk)
      simpa [pow_two] using this
  have : Nat.ceil (Real.sqrt (q : ℝ)) ≤ k := Nat.ceil_le.2 h_sqrt_le
  simpa [hk] using this

lemma riemann_hypothesis_stepanov_bound
  (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q : ℕ) (a : F)
  (hq : q = Fintype.card F)
  (hm3 : 3 ≤ f.natDegree)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (hq6m : q > 6 * f.natDegree)
  [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) a)] :
  (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
    < (q : ℝ) / 2 + 2 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  set m : ℕ := f.natDegree with hm_def
  have h18_lt_q : 18 < q := by
    have : 18 ≤ 6 * m := by
      have : 3 ≤ m := by simpa [hm_def] using hm3
      have := Nat.mul_le_mul_left 6 this
      simpa using this
    exact lt_of_le_of_lt this (by simpa [hm_def] using hq6m)
  have h15_le_q : (15 : ℕ) ≤ q :=
    le_trans (by decide : (15 : ℕ) ≤ 19) (Nat.succ_le_of_lt h18_lt_q)
  have hq_pos_nat : 0 < q := lt_trans (by decide : 0 < 18) h18_lt_q
  set ℓ : ℕ := Nat.ceil (Real.sqrt q) with hℓ_def
  have hℓ_le_q_div3 : ℓ ≤ q / 3 := by
    simpa [ℓ, hℓ_def] using ceil_sqrt_le_div_three q h15_le_q
  have h_sqrt_le_ℓ : Real.sqrt q ≤ (ℓ : ℝ) := by
    have hceil : Real.sqrt q ≤ (Nat.ceil (Real.sqrt q) : ℝ) :=
      Nat.le_ceil (Real.sqrt q)
    simpa [ℓ, hℓ_def] using hceil
  have hℓ_pos_real : 0 < (ℓ : ℝ) :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr (by exact_mod_cast hq_pos_nat)) h_sqrt_le_ℓ
  have hℓ_pos : 0 < ℓ := by exact_mod_cast hℓ_pos_real
  obtain ⟨R, hR_ne, hdegR, hvan⟩ :=
    stepanov_polynomial (F := F) (hF := hF) (f := f) (q := q) (ℓ := ℓ) (a := a)
      hq hm3 hnsq hq6m hℓ_pos hℓ_le_q_div3
  set Sfin : Finset F :=
    Finset.univ.filter (fun x : F => x ∈ S_a F f ((q - 1) / 2) a) with hSfin_def
  have hvan_S : ∀ x ∈ Sfin, ∀ k < ℓ, (hasseDerivOp F k R).eval x = 0 := by
    intro x hx k hk
    rcases Finset.mem_filter.mp hx with ⟨_, hx_sa⟩
    exact hvan x hx_sa k hk
  have h_card_Sfin_le :
      (Sfin.card : ℝ) ≤ (R.natDegree : ℝ) / (ℓ : ℝ) :=
    hasse_vanishing_card_bound (F := F) (r := R) (ℓ := ℓ) (S := Sfin)
      hR_ne hℓ_pos hvan_S
  have h_card_subtype_eq :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
        = (Sfin.card : ℝ) := by
    exact_mod_cast (by
      simp [Sfin] :
        Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} = Sfin.card)
  have h_card_le :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
        ≤ (R.natDegree : ℝ) / (ℓ : ℝ) := by
    simpa [h_card_subtype_eq] using h_card_Sfin_le
  have hdegR' :
      (R.natDegree : ℝ)
        < (m : ℝ) * (q : ℝ)
          + (ℓ : ℝ) * (q : ℝ) / 2
          + (ℓ : ℝ) ^ 2 * (m : ℝ) := by
    have hfdeg : f.natDegree = m := by simp [hm_def]
    have h1 : ((f.natDegree * q : ℕ) : ℝ) = (m : ℝ) * (q : ℝ) := by
      simp [hfdeg, Nat.cast_mul, mul_comm]
    have h2 : ((ℓ * q : ℕ) : ℝ) = (ℓ : ℝ) * (q : ℝ) := by
      simp [Nat.cast_mul, mul_comm]
    have h3 : ((ℓ * ℓ * f.natDegree : ℕ) : ℝ)
        = (ℓ : ℝ) ^ 2 * (m : ℝ) := by
      simp [hfdeg, Nat.cast_mul, pow_two, mul_comm]
    simpa [h1, h2, h3] using hdegR
  have hq_le_ℓsq : (q : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
    have h_sq_le :
        Real.sqrt q * Real.sqrt q ≤ (ℓ : ℝ) * (ℓ : ℝ) :=
      mul_self_le_mul_self (a := Real.sqrt q) (b := (ℓ : ℝ))
        (Real.sqrt_nonneg _) h_sqrt_le_ℓ
    have hsq_eq : Real.sqrt q * Real.sqrt q = (q : ℝ) := by simp
    simpa [hsq_eq, pow_two] using h_sq_le
  have h_mq_le_mℓsq :
      (m : ℝ) * (q : ℝ)
        ≤ (m : ℝ) * (ℓ : ℝ) ^ 2 := by
    have :=
      mul_le_mul_of_nonneg_left hq_le_ℓsq
        (by exact_mod_cast (Nat.zero_le m) : 0 ≤ (m : ℝ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hdegR_upper :
      (R.natDegree : ℝ)
        < (ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
    have h1 :
        (m : ℝ) * (q : ℝ) + (ℓ : ℝ) ^ 2 * (m : ℝ)
          ≤ (m : ℝ) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (m : ℝ) :=
      add_le_add_right h_mq_le_mℓsq _
    have h2 :
        (m : ℝ) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (m : ℝ)
          = 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      calc
        (m : ℝ) * (ℓ : ℝ) ^ 2 + (ℓ : ℝ) ^ 2 * (m : ℝ)
            = (m : ℝ) * (ℓ : ℝ) ^ 2 + (m : ℝ) * (ℓ : ℝ) ^ 2 := by
              simp [mul_comm]
        _ = 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by ring
    have h3 :
        (m : ℝ) * (q : ℝ) + (ℓ : ℝ) ^ 2 * (m : ℝ)
          ≤ 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      simpa [h2] using h1
    have h4 :
        (m : ℝ) * (q : ℝ) + (ℓ : ℝ) * (q : ℝ) / 2
          + (ℓ : ℝ) ^ 2 * (m : ℝ)
          ≤ (ℓ : ℝ) * (q : ℝ) / 2
            + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2 := by
      have := add_le_add_left h3 ((ℓ : ℝ) * (q : ℝ) / 2)
      simpa [add_comm, add_left_comm, add_assoc] using this
    exact lt_of_lt_of_le hdegR' h4
  have hdeg_div_main :
      (R.natDegree : ℝ) / (ℓ : ℝ)
        < (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
    have hdeg_div :
        (R.natDegree : ℝ) / (ℓ : ℝ)
          < ((ℓ : ℝ) * (q : ℝ) / 2
              + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ) := by
      have := mul_lt_mul_of_pos_right hdegR_upper (inv_pos.mpr hℓ_pos_real)
      simpa [div_eq_mul_inv] using this
    have h_upper_simpl :
        ((ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
          = (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
      have hneq : (ℓ : ℝ) ≠ 0 := ne_of_gt hℓ_pos_real
      calc
        ((ℓ : ℝ) * (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
            = (ℓ : ℝ) * (q : ℝ) / 2 / (ℓ : ℝ)
                + (2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ) := by
                  field_simp [add_comm, add_left_comm, add_assoc]
        _ = (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) := by
          have h1 : (ℓ : ℝ) * (q : ℝ) / 2 / (ℓ : ℝ) = (q : ℝ) / 2 := by
            field_simp [hneq, mul_comm, mul_left_comm, mul_assoc]
          have h2 : (2 * (m : ℝ) * (ℓ : ℝ) ^ 2) / (ℓ : ℝ)
              = 2 * (m : ℝ) * (ℓ : ℝ) := by
            field_simp [hneq, pow_two, mul_comm, mul_left_comm, mul_assoc]
          simp [h1, h2]
    simpa [h_upper_simpl] using hdeg_div
  have :
      (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
        < (q : ℝ) / 2 + 2 * (m : ℝ) * (ℓ : ℝ) :=
    lt_of_le_of_lt h_card_le hdeg_div_main
  simpa [m, hm_def, ℓ, hℓ_def] using this

lemma riemann_hypothesis_upper_bound
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      < (q : ℝ) + 4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  classical
  set c := (q - 1) / 2 with hc_def
  set m := f.natDegree with hm_def
  have h_stepanov := riemann_hypothesis_stepanov_bound F hF f q 1 hq hm3 hnsq hq6m
  let curveSet := {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f}
  let S1_set := {x : F // x ∈ S_a F f c 1}
  have h_two_S1_bound :
      2 * (Fintype.card S1_set : ℝ) <
        (q : ℝ) + 4 * (m : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by
    simp [hm_def, hc_def, S1_set] at h_stepanov ⊢
    linarith [h_stepanov]
  have h_N_le_2S1 : (Fintype.card curveSet : ℝ) ≤ 2 * (Fintype.card S1_set : ℝ) := by
    have h_proj : ∀ p : curveSet, (p.val.1 : F) ∈ S_a F f c 1 := by
      intro ⟨⟨x, y⟩, hp⟩
      simp [S_a]
      by_cases hfx : Polynomial.eval x f = 0
      · left; exact hfx
      · right
        have hfx_sq : IsSquare (Polynomial.eval x f) :=
          ⟨y, by ring_nf; simpa using hp.symm⟩
        have hfx_ne : Polynomial.eval x f ≠ 0 := hfx
        rw [FiniteField.isSquare_iff hodd hfx_ne] at hfx_sq
        have hcard_eq : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
          have hcard_pos : 0 < Fintype.card F := Fintype.card_pos
          have : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hodd
          omega
        rw [hcard_eq] at hfx_sq
        simpa [hc_def, hq] using hfx_sq
    let proj : curveSet → S1_set := fun p => ⟨p.val.1, h_proj p⟩
    have h_count : Fintype.card curveSet ≤ 2 * Fintype.card S1_set := by
      have h_sigma : Fintype.card curveSet =
          Fintype.card ((y : S1_set) × {x : curveSet // proj x = y}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv proj).symm
      rw [h_sigma, Fintype.card_sigma]
      have h_fiber_le : ∀ y : S1_set, Fintype.card {x : curveSet // proj x = y} ≤ 2 := by
        intro ⟨x, hx⟩
        have h_card_sq_roots : Fintype.card {y' : F // y' ^ 2 = Polynomial.eval x f} ≤ 2 := by
          by_cases h0 : Polynomial.eval x f = 0
          · have h_unique : {y' : F // y' ^ 2 = Polynomial.eval x f} ≃ {y' : F // y' = 0} := by
              refine Equiv.subtypeEquiv (Equiv.refl F) ?_
              intro y'
              simp only [Equiv.refl_apply, h0, sq_eq_zero_iff]
            rw [Fintype.card_congr h_unique, Fintype.card_unique]
            norm_num
          · let p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C (Polynomial.eval x f)
            have hp_ne : p ≠ 0 := by
              simp only [p, ne_eq, sub_eq_zero]
              intro h_eq
              have h_deg1 : (Polynomial.X ^ 2 : Polynomial F).natDegree = 2 :=
                Polynomial.natDegree_X_pow 2
              have h_deg2 : (Polynomial.C (Polynomial.eval x f) : Polynomial F).natDegree = 0 :=
                Polynomial.natDegree_C _
              have : (2 : ℕ) = 0 := by rw [← h_deg1, h_eq, h_deg2]
              norm_num at this
            have h_deg : p.natDegree ≤ 2 := by
              simp only [p]
              calc (Polynomial.X ^ 2 - Polynomial.C (Polynomial.eval x f)).natDegree
                  ≤ max (Polynomial.X ^ 2 : Polynomial F).natDegree
                      (Polynomial.C (Polynomial.eval x f)).natDegree :=
                    Polynomial.natDegree_sub_le _ _
                _ = max 2 0 := by simp [Polynomial.natDegree_C]
                _ = 2 := by norm_num
            have h_roots : ∀ y' : F, p.IsRoot y' ↔ y' ^ 2 = Polynomial.eval x f := by
              intro y'
              simp only [p, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
                Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
            have h_card_roots : Multiset.card p.roots ≤ p.natDegree := Polynomial.card_roots' p
            have h_inj : Function.Injective (fun (y' : {y' : F // y' ^ 2 = Polynomial.eval x f}) =>
                (⟨y'.val, (Polynomial.mem_roots hp_ne).mpr ((h_roots y'.val).mpr y'.property)⟩ :
                  {y' : F // y' ∈ p.roots})) := by
              intro ⟨a, ha⟩ ⟨b, hb⟩ h
              simp only [Subtype.mk.injEq] at h
              exact Subtype.ext h
            have h_card_le_roots : Fintype.card {y' : F // y' ^ 2 = Polynomial.eval x f} ≤
                Fintype.card {y' : F // y' ∈ p.roots} := Fintype.card_le_of_injective _ h_inj
            have h_fintype_le_multiset :
                Fintype.card {y' : F // y' ∈ p.roots} ≤ Multiset.card p.roots := by
              calc Fintype.card {y' : F // y' ∈ p.roots}
                  ≤ Fintype.card p.roots.toFinset := by
                    refine Fintype.card_le_of_injective
                      (fun ⟨y', hy'⟩ => ⟨y', Multiset.mem_toFinset.mpr hy'⟩) ?_
                    intro ⟨a, ha⟩ ⟨b, hb⟩ h
                    simp only [Subtype.mk.injEq] at h
                    exact Subtype.ext h
                _ = p.roots.toFinset.card := Fintype.card_coe p.roots.toFinset
                _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le p.roots
            calc Fintype.card {y' : F // y' ^ 2 = Polynomial.eval x f}
                ≤ Fintype.card {y' : F // y' ∈ p.roots} := h_card_le_roots
              _ ≤ Multiset.card p.roots := h_fintype_le_multiset
              _ ≤ p.natDegree := h_card_roots
              _ ≤ 2 := h_deg
        have h_fiber_inj : Function.Injective (fun (p' : {p' : curveSet // proj p' = ⟨x, hx⟩}) =>
            (⟨p'.val.val.2, by
              have hp := p'.val.property
              have hpx : proj p'.val = ⟨x, hx⟩ := p'.property
              simp only [proj] at hpx
              have hx_eq : p'.val.val.1 = x := Subtype.ext_iff.mp hpx
              simp only [hx_eq] at hp
              exact hp⟩ : {y' : F // y' ^ 2 = Polynomial.eval x f})) := by
          intro ⟨⟨⟨x1, y1⟩, hp1⟩, hproj1⟩ ⟨⟨⟨x2, y2⟩, hp2⟩, hproj2⟩ h
          simp only [Subtype.mk.injEq] at h
          simp only [proj] at hproj1 hproj2
          have hx1_eq : x1 = x := Subtype.ext_iff.mp hproj1
          have hx2_eq : x2 = x := Subtype.ext_iff.mp hproj2
          simp only [Subtype.mk.injEq]
          refine Subtype.ext ?_
          simp only [Prod.mk.injEq]
          exact ⟨hx1_eq.trans hx2_eq.symm, h⟩
        exact le_trans (Fintype.card_le_of_injective _ h_fiber_inj) h_card_sq_roots
      calc ∑ y : S1_set, Fintype.card {x : curveSet // proj x = y}
          ≤ ∑ _ : S1_set, 2 := Finset.sum_le_sum (fun y _ => h_fiber_le y)
        _ = 2 * Fintype.card S1_set := by simp [Finset.sum_const, Finset.card_univ]; ring
    exact_mod_cast h_count
  have h := lt_of_le_of_lt h_N_le_2S1 h_two_S1_bound
  simpa [curveSet, S1_set, hc_def, hm_def] using h

lemma curve_count_ge_two_times_N1
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      ≥
        2 *
          (Fintype.card
              {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧
                Polynomial.eval x f ≠ 0} : ℝ) :=
by
  classical
  subst hq
  set c := (Fintype.card F - 1) / 2 with hc_def
  let N1 := {x : F // (Polynomial.eval x f) ^ c = 1 ∧ Polynomial.eval x f ≠ 0}
  let C := {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f}
  let C_from_N1 :=
    {p : C // p.val.1 ∈ {x : F | (Polynomial.eval x f) ^ c = 1 ∧ Polynomial.eval x f ≠ 0}}
  have h1 : Fintype.card C ≥ Fintype.card C_from_N1 :=
    Fintype.card_le_of_embedding (Function.Embedding.subtype _)
  have hcard_div : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    have _ := FiniteField.odd_card_of_char_ne_two hodd
    have _ : 0 < Fintype.card F := Fintype.card_pos
    omega
  have h2 : Fintype.card C_from_N1 = 2 * Fintype.card N1 := by
    let proj : C_from_N1 → N1 := fun ⟨⟨⟨x, y⟩, hp⟩, hx⟩ => ⟨x, hx⟩
    have h_fiber_card : ∀ x : N1, Fintype.card {p : C_from_N1 // proj p = x} = 2 := by
      intro ⟨x, ⟨hxc, hx_ne⟩⟩
      have hfx_ne : Polynomial.eval x f ≠ 0 := hx_ne
      have h_euler := FiniteField.isSquare_iff hodd hfx_ne
      rw [hcard_div] at h_euler
      have hfx_sq : IsSquare (Polynomial.eval x f) := h_euler.mpr hxc
      obtain ⟨r, hr⟩ := hfx_sq.exists_mul_self
      have hr' : r ^ 2 = Polynomial.eval x f := by rw [sq]; exact hr.symm
      have hr_ne : r ≠ 0 := by
        intro h; rw [h, sq, mul_zero] at hr'; exact hfx_ne hr'.symm
      have h_roots : ∀ y : F, y ^ 2 = Polynomial.eval x f ↔ y = r ∨ y = -r := by
        intro y
        constructor
        · intro hy
          have : y ^ 2 = r ^ 2 := by
            simpa [hr'.symm] using hy
          rw [sq_eq_sq_iff_eq_or_eq_neg] at this
          exact this
        · intro h_or
          cases h_or with
          | inl h => rw [h, hr']
          | inr h => rw [h, neg_sq, hr']
      have hr_ne_neg : r ≠ -r := by
        intro h
        have h2r : r + r = 0 := by
          have : r - (-r) = 0 := sub_eq_zero.mpr h
          simp only [sub_neg_eq_add] at this
          exact this
        have h2_times_r : (2 : F) * r = 0 := by rw [two_mul]; exact h2r
        rw [mul_eq_zero] at h2_times_r
        cases h2_times_r with
        | inl h2 =>
          have := CharP.ringChar_of_prime_eq_zero (R := F) Nat.prime_two h2
          exact hodd this
        | inr h0 => exact hr_ne h0
      have h_sq_roots : Fintype.card {y : F // y ^ 2 = Polynomial.eval x f} = 2 := by
        have h_equiv : {y : F // y ^ 2 = Polynomial.eval x f} ≃ ({r, -r} : Finset F) := by
          refine {
            toFun := fun ⟨y, hy⟩ => by
              have hy_or := (h_roots y).mp hy
              refine ⟨y, ?_⟩
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact hy_or
            invFun := fun ⟨y, hy⟩ => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              refine ⟨y, (h_roots y).mpr hy⟩
            left_inv := fun ⟨y, hy⟩ => by simp
            right_inv := fun ⟨y, hy⟩ => by simp
          }
        rw [Fintype.card_congr h_equiv]
        have : ({r, -r} : Finset F).card = 2 := by
          rw [Finset.card_insert_of_notMem, Finset.card_singleton]
          simp only [Finset.mem_singleton]
          exact hr_ne_neg
        simp only [Fintype.card_coe]
        exact this
      have h_fiber_equiv : {p : C_from_N1 // proj p = ⟨x, ⟨hxc, hx_ne⟩⟩} ≃
          {y : F // y ^ 2 = Polynomial.eval x f} := by
        refine {
          toFun := fun ⟨⟨⟨⟨x', y⟩, hp⟩, hx'⟩, hproj⟩ => by
            simp only [proj] at hproj
            have hx'_eq : x' = x := Subtype.ext_iff.mp hproj
            exact ⟨y, by simp only [← hx'_eq]; exact hp⟩
          invFun := fun ⟨y, hy⟩ => by
            refine ⟨⟨⟨⟨x, y⟩, hy⟩, ?_⟩, rfl⟩
            simp only [Set.mem_setOf_eq]
            exact ⟨hxc, hx_ne⟩
          left_inv := by
            intro ⟨⟨⟨⟨x', y⟩, hp⟩, hx'⟩, hproj⟩
            simp only [proj] at hproj
            have hx'_eq : x' = x := Subtype.ext_iff.mp hproj
            simp only [Subtype.mk.injEq]
            subst hx'_eq
            rfl
          right_inv := fun ⟨y, hy⟩ => rfl
        }
      rw [Fintype.card_congr h_fiber_equiv, h_sq_roots]
    calc
      Fintype.card C_from_N1
          = Fintype.card ((x : N1) × {p : C_from_N1 // proj p = x}) := by
            exact Fintype.card_congr (Equiv.sigmaFiberEquiv proj).symm
      _ = ∑ x : N1, Fintype.card {p : C_from_N1 // proj p = x} := Fintype.card_sigma
      _ = ∑ _x : N1, 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact h_fiber_card x
      _ = 2 * Fintype.card N1 := by
          simp [Finset.sum_const, Finset.card_univ, mul_comm]
  have h3 : (Fintype.card C : ℝ) ≥ 2 * (Fintype.card N1 : ℝ) := by
    have h3' : (Fintype.card C : ℝ) ≥ (Fintype.card C_from_N1 : ℝ) := by exact_mod_cast h1
    simpa [h2, Nat.cast_mul] using h3'
  simpa [C, N1, hc_def] using h3

lemma partition_N1_eq_q_sub_S_neg1
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hodd : ringChar F ≠ 2)
    [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) (-1))] :
    (Fintype.card
        {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧
          Polynomial.eval x f ≠ 0} : ℝ)
      = (q : ℝ) -
        (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) (-1)} : ℝ) :=
by
  subst hq
  set c := (Fintype.card F - 1) / 2 with hc_def
  have hcard_div : Fintype.card F / 2 = (Fintype.card F - 1) / 2 := by
    have _ := FiniteField.odd_card_of_char_ne_two hodd
    have _ : 0 < Fintype.card F := Fintype.card_pos
    omega
  have h1_ne_neg1 : (1 : F) ≠ -1 := by
    intro h
    have h2 : (2 : F) = 0 := by
      calc
        (2 : F) = 1 - (-1) := by ring
        _ = 1 - 1 := by rw [← h]
        _ = 0 := by ring
    exact hodd (CharP.ringChar_of_prime_eq_zero (R := F) Nat.prime_two h2)
  let N1 :=
    Finset.univ.filter (fun x : F => (Polynomial.eval x f) ^ c = 1 ∧
      Polynomial.eval x f ≠ 0)
  let Sn1 := Finset.univ.filter (fun x : F => x ∈ S_a F f c (-1))
  have h_compl : N1 = Sn1ᶜ := by
    ext x
    simp [N1, Sn1, S_a]
    constructor
    · rintro ⟨h1, hne⟩
      refine ⟨hne, ?_⟩
      intro hm1
      exact h1_ne_neg1 (h1.symm.trans hm1)
    · intro h
      have h' : Polynomial.eval x f ≠ 0 ∧
          (Polynomial.eval x f) ^ c ≠ -1 := by
        simpa [not_or] using h
      have h_euler := FiniteField.pow_dichotomy hodd h'.1
      rw [hcard_div] at h_euler
      rcases h_euler with h1 | hm1'
      · exact ⟨h1, h'.1⟩
      · exact (h'.2 hm1').elim
  have hN1_card_real :
      (N1.card : ℝ) = (Fintype.card F : ℝ) - (Sn1.card : ℝ) := by
    have hN1_card : N1.card = Fintype.card F - Sn1.card := by
      simp [h_compl, Finset.card_compl]
    have hSn1_le : Sn1.card ≤ Fintype.card F :=
      Finset.card_le_card (Finset.subset_univ _)
    simp [hN1_card, Nat.cast_sub hSn1_le]
  have h_N1_eq :
      Fintype.card {x : F // (Polynomial.eval x f) ^ c = 1 ∧
        Polynomial.eval x f ≠ 0} = N1.card :=
    Fintype.card_subtype _
  have h_S_eq :
      Fintype.card {x : F // x ∈ S_a F f c (-1)} = Sn1.card :=
    Fintype.card_subtype _
  simp only [hc_def] at h_N1_eq h_S_eq
  convert
      (by
        simp only [h_N1_eq, h_S_eq, hN1_card_real] :
          (Fintype.card {x : F // (Polynomial.eval x f) ^
              ((Fintype.card F - 1) / 2) = 1 ∧
              Polynomial.eval x f ≠ 0} : ℝ) =
            (Fintype.card F : ℝ) -
              (Fintype.card {x : F // x ∈ S_a F f
                ((Fintype.card F - 1) / 2) (-1)} : ℝ)) using 4

lemma riemann_hypothesis_lower_bound
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      > (q : ℝ) - 4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) :=
by
  classical
  linarith [ curve_count_ge_two_times_N1 F f q hq hodd,
            partition_N1_eq_q_sub_S_neg1 F f q hq hodd,
            riemann_hypothesis_stepanov_bound F hF f q (-1) hq hm3 hnsq hq6m ]

theorem riemann_hypothesis_hec
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) :
    |((q : ℝ) - (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ))|
      < (5 : ℝ) * (f.natDegree : ℝ) * Real.sqrt (q : ℝ) :=
by
  have hm_pos : (0 : ℝ) < (f.natDegree : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num) hm3)
  have hq_pos : (0 : ℝ) < (q : ℝ) :=
    Nat.cast_pos.mpr
      (Nat.lt_trans (Nat.mul_pos (by norm_num)
        (Nat.lt_of_lt_of_le (by norm_num) hm3)) hq6m)
  by_cases hchar2 : ringChar F = 2
  · have hN_eq_q :
        Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} = q := by
      haveI : CharP F 2 := hchar2 ▸ ringChar.charP F
      haveI : ExpChar F 2 := .prime Nat.prime_two
      let frob := frobeniusEquiv F 2
      simpa [hq] using
        (Fintype.card_congr {
          toFun := fun ⟨⟨x, _⟩, _⟩ => x
          invFun := fun x => ⟨(x, frob.symm (Polynomial.eval x f)), frob.apply_symm_apply _⟩
          left_inv := fun ⟨⟨_, _⟩, hy⟩ =>
            Subtype.ext (Prod.ext rfl (frob.injective
              (by
                simp only [frobeniusEquiv_def, hy, frob,
                  RingEquiv.apply_symm_apply])))
          right_inv := fun _ => rfl
        })
    simp [hN_eq_q, sub_self, abs_zero]
    positivity
  · set N : ℝ :=
      (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
    have h_abs :
        |(q : ℝ) - N| <
          4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by
      have h_upper :=
        riemann_hypothesis_upper_bound F hchar2 f q hq hm3 hnsq hq6m hchar2
      have h_lower :=
        riemann_hypothesis_lower_bound F hchar2 f q hq hm3 hnsq hq6m hchar2
      rw [abs_sub_lt_iff]; constructor <;> linarith
    have h_ceil_bound : (Nat.ceil (Real.sqrt q) : ℝ) ≤ Real.sqrt q + 1 := by
      have := Nat.ceil_lt_add_one (Real.sqrt_nonneg q)
      linarith
    have h_q_ge_18 : (18 : ℕ) ≤ q := by
      have : 6 * 3 ≤ 6 * f.natDegree := Nat.mul_le_mul_left 6 hm3
      omega
    have h_sqrt_gt_4 : (4 : ℝ) < Real.sqrt q := by
      rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
      apply Real.sqrt_lt_sqrt (by norm_num)
      exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 16 < 18) h_q_ge_18
    calc
      |(q : ℝ) - N| <
          4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := h_abs
      _ ≤ 4 * (f.natDegree : ℝ) * (Real.sqrt q + 1) := by
        nlinarith [h_ceil_bound]
      _ = 4 * (f.natDegree : ℝ) * Real.sqrt q +
            4 * (f.natDegree : ℝ) := by ring
      _ < 4 * (f.natDegree : ℝ) * Real.sqrt q +
            (f.natDegree : ℝ) * Real.sqrt q := by
        nlinarith [hm_pos, h_sqrt_gt_4]
      _ = 5 * (f.natDegree : ℝ) * Real.sqrt q := by ring

#print axioms riemann_hypothesis_hec
