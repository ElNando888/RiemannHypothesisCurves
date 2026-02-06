import Mathlib

noncomputable def hasseDerivOp (F : Type*) [Field F] (k : ℕ) : Polynomial F → Polynomial F :=
  Polynomial.hasseDeriv k

lemma sum_hasseDeriv_piAntidiag_eq_sum_fin
    (F : Type*) [Field F] (k r : ℕ) (f : Fin r → Polynomial F) :
    (∑ j ∈ ((Finset.univ : Finset (Fin r)).piAntidiag k),
        (Finset.univ : Finset (Fin r)).prod
          (fun i => hasseDerivOp F (j i) (f i)))
      =
      (∑ j ∈ (((Finset.univ : Finset (Fin r → Fin (k + 1)))).filter
                  (fun j =>
                    ((Finset.univ : Finset (Fin r)).sum (fun i => (j i).val)) = k)),
          (Finset.univ : Finset (Fin r)).prod
            (fun i => hasseDerivOp F ((j i).val) (f i))) :=
by
  let phi :
      (j : Fin r → ℕ) →
      j ∈ ((Finset.univ : Finset (Fin r)).piAntidiag k) →
      (Fin r → Fin (k + 1)) :=
    fun j hj i =>
      ⟨j i,
        Nat.lt_succ_of_le <|
          by
            have hj_sum :
                (Finset.univ : Finset (Fin r)).sum j = k :=
              (Finset.mem_piAntidiag.mp hj).1
            simpa [hj_sum] using
              (Finset.single_le_sum_of_canonicallyOrdered
                (f := j) (s := (Finset.univ : Finset (Fin r))) (i := i) (by simp))⟩
  refine
    Finset.sum_bij (fun j hj => phi j hj) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_piAntidiag.mp hj with ⟨hj_sum, -⟩
    simp [phi, hj_sum]
  · intro j₁ _ j₂ _ h_eq
    funext i
    simpa [phi] using congrArg (fun g => (g i).val) h_eq
  · intro j' hj'
    refine ⟨fun i => (j' i).val, ?_, ?_⟩
    · rcases Finset.mem_filter.mp hj' with ⟨_, hP⟩
      refine Finset.mem_piAntidiag.mpr ?_
      refine ⟨hP, ?_⟩
      intro i _
      simp
    · ext i
      simp [phi]
  · intro j _
    simp [phi]

lemma hasseLeibniz_general (F : Type*) [Field F] (k r : ℕ) (f : Fin r → Polynomial F) :
  hasseDerivOp F k ((Finset.univ : Finset (Fin r)).prod (fun i => f i)) =
    Finset.sum
      (((Finset.univ : Finset (Fin r → Fin (k + 1)))).filter
        (fun j => ((Finset.univ : Finset (Fin r)).sum (fun i => (j i).val)) = k))
      (fun j => (Finset.univ : Finset (Fin r)).prod
        (fun i => hasseDerivOp F ((j i).val) (f i))) :=
by
  have hasseLeibniz_piAntidiag_finset :
      ∀ (s : Finset (Fin r)) (k : ℕ),
        hasseDerivOp F k (s.prod f) =
          ∑ j ∈ s.piAntidiag k,
            s.prod fun i => hasseDerivOp F (j i) (f i) := by
    intro s
    refine Finset.cons_induction ?h_empty ?h_cons s
    · intro k
      cases k with
      | zero =>
          simp [hasseDerivOp]
      | succ k =>
          simpa [hasseDerivOp,
            Finset.piAntidiag_empty_of_ne_zero (Nat.succ_ne_zero _)] using
            (Polynomial.hasseDeriv_C (R := F) (k := Nat.succ k) (r := (1 : F))
              (Nat.succ_pos _))
    · intro a s ha ih k
      let u : Finset (Fin r) := Finset.cons a s ha
      have hmul :
          hasseDerivOp F k (u.prod f) =
            ∑ p ∈ Finset.antidiagonal k,
              hasseDerivOp F p.1 (f a) *
                hasseDerivOp F p.2 (s.prod f) := by
        have hprod : u.prod f = f a * s.prod f := by
          simpa [u] using
            (Finset.prod_cons (s := s) (a := a) (f := f) ha)
        simpa [hasseDerivOp, hprod] using
          (Polynomial.hasseDeriv_mul (R := F) (k := k)
            (f := f a) (g := s.prod f))
      have hL :
          hasseDerivOp F k (u.prod f) =
            ∑ p ∈ Finset.antidiagonal k,
              hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
        refine (hmul.trans ?_)
        refine Finset.sum_congr rfl ?_
        intro p hp
        simp [ih p.2]
      let w : (Fin r → ℕ) → Polynomial F :=
        fun j => u.prod fun i => hasseDerivOp F (j i) (f i)
      have hR1 :
          ∑ j ∈ u.piAntidiag k, w j =
            ∑ p ∈ Finset.antidiagonal k,
              ∑ j ∈ (s.piAntidiag p.2).map
                      (addRightEmbedding (fun t => if t = a then p.1 else 0)),
                w j := by
        let t : (ℕ × ℕ) → Finset (Fin r → ℕ) :=
          fun p =>
            (s.piAntidiag p.2).map
              (addRightEmbedding (fun t => if t = a then p.1 else 0))
        have hpw :
            (↑(Finset.antidiagonal k) : Set (ℕ × ℕ)).PairwiseDisjoint t := by
          simpa [t] using
            (Finset.pairwiseDisjoint_piAntidiag_map_addRightEmbedding
              (i := a) (s := s) (hi := ha) (n := k))
        have hsd :
            ∑ j ∈ (Finset.antidiagonal k).biUnion t, w j =
              ∑ p ∈ Finset.antidiagonal k,
                ∑ j ∈ t p, w j := by
          simpa [t] using
            (Finset.sum_biUnion
              (s := Finset.antidiagonal k)
              (t := t)
              (hs := hpw)
              (f := w))
        have hpi :
            u.piAntidiag k = (Finset.antidiagonal k).biUnion t := by
          simpa [u, t, Finset.disjiUnion_eq_biUnion] using
            (Finset.piAntidiag_cons (i := a) (s := s) (hi := ha) (n := k))
        simpa [hpi, t] using hsd
      have h_inner :
          ∀ p ∈ Finset.antidiagonal k,
            (∑ j ∈ (s.piAntidiag p.2).map
                      (addRightEmbedding (fun t => if t = a then p.1 else 0)),
                w j) =
              hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
        intro p hp
        let e : (Fin r → ℕ) ↪ (Fin r → ℕ) :=
          addRightEmbedding (fun t => if t = a then p.1 else 0)
        have h_pointwise :
            ∀ g ∈ s.piAntidiag p.2,
              w (e g) =
                hasseDerivOp F p.1 (f a) *
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
          intro g hg
          obtain ⟨-, hmem⟩ : s.sum g = p.2 ∧ ∀ i, g i ≠ 0 → i ∈ s := by
            simpa [Finset.mem_piAntidiag] using hg
          have hga : g a = 0 := by
            by_contra hne
            exact ha (hmem a hne)
          have hsplit :
              u.prod (fun i => hasseDerivOp F (e g i) (f i)) =
                hasseDerivOp F (e g a) (f a) *
                  s.prod fun i => hasseDerivOp F (e g i) (f i) := by
            simpa [u] using
              (Finset.prod_cons
                (s := s) (a := a)
                (f := fun i => hasseDerivOp F (e g i) (f i))
                ha)
          have h_on_s :
              ∀ i ∈ s, e g i = g i := by
            intro i hi
            have hne : i ≠ a := by
              intro h
              subst h
              exact ha hi
            simp [e, hne]
          have hprod_s :
              s.prod (fun i => hasseDerivOp F (e g i) (f i)) =
                s.prod fun i => hasseDerivOp F (g i) (f i) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            simp [h_on_s i hi]
          have h_at_a : e g a = p.1 := by
            simp [e, hga]
          simp [w, hsplit, h_at_a, hprod_s]
        calc
          ∑ j ∈ (s.piAntidiag p.2).map
                    (addRightEmbedding (fun t => if t = a then p.1 else 0)),
                w j =
              ∑ g ∈ s.piAntidiag p.2, w (e g) := by simp [w, e]
          _ =
              ∑ g ∈ s.piAntidiag p.2,
                hasseDerivOp F p.1 (f a) *
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
                refine Finset.sum_congr rfl ?_
                intro g hg
                simpa using h_pointwise g hg
          _ = hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
                simp [Finset.mul_sum]
      have hR :
          ∑ j ∈ u.piAntidiag k, w j =
            ∑ p ∈ Finset.antidiagonal k,
              hasseDerivOp F p.1 (f a) *
                ∑ g ∈ s.piAntidiag p.2,
                  s.prod fun i => hasseDerivOp F (g i) (f i) := by
        refine (hR1.trans ?_)
        refine Finset.sum_congr rfl ?_
        intro p hp
        simpa using h_inner p hp
      simpa [u, w] using hL.trans hR.symm
  simpa using
    (hasseLeibniz_piAntidiag_finset (Finset.univ : Finset (Fin r)) k).trans
      (sum_hasseDeriv_piAntidiag_eq_sum_fin F k r f)

lemma hasseDerivOp_X_sub_C_pow (F : Type*) [Field F]
    (k r : ℕ) (hk : k ≤ r) :
    ∀ a : F,
      hasseDerivOp F k ((Polynomial.X - Polynomial.C a)^r) =
        Polynomial.C (Nat.choose r k : F) * (Polynomial.X - Polynomial.C a)^(r - k) :=
by
  intro a
  ext n
  have hL :
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
        ((n + k).choose k : F) *
          ((Polynomial.X - Polynomial.C a) ^ r).coeff (n + k) := by
    simpa [hasseDerivOp] using
      (Polynomial.hasseDeriv_coeff (k := k)
        (f := (Polynomial.X - Polynomial.C a) ^ r) (n := n))
  have hcoeff_pow :
      ((Polynomial.X - Polynomial.C a) ^ r).coeff (n + k) =
        (-a) ^ (r - (n + k)) * (Nat.choose r (n + k) : F) := by
    simpa [sub_eq_add_neg] using
      (Polynomial.coeff_X_add_C_pow (R := F) (-a) r (n + k))
  have hcoeff_pow2 :
      ((Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n =
        (-a) ^ ((r - k) - n) * (Nat.choose (r - k) n : F) := by
    simpa [sub_eq_add_neg] using
      (Polynomial.coeff_X_add_C_pow (R := F) (-a) (r - k) n)
  have hL' :
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
        (-a) ^ (r - (n + k)) *
          (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) := by
    calc
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
          ((n + k).choose k : F) *
            ((Polynomial.X - Polynomial.C a) ^ r).coeff (n + k) := hL
      _ = ((n + k).choose k : F) *
            ((-a) ^ (r - (n + k)) * (Nat.choose r (n + k) : F)) := by
            simp [hcoeff_pow]
      _ = (-a) ^ (r - (n + k)) *
            (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) := by
            ring
  have hR' :
      (Polynomial.C (Nat.choose r k : F) *
          (Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n =
        (-a) ^ (r - (n + k)) *
          ((Nat.choose r k : F) * (Nat.choose (r - k) n : F)) := by
    calc
      (Polynomial.C (Nat.choose r k : F) *
            (Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n =
          (Nat.choose r k : F) *
            ((Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n := by
            simp
      _ = (Nat.choose r k : F) *
            ((-a) ^ ((r - k) - n) * (Nat.choose (r - k) n : F)) := by
            simp [hcoeff_pow2]
      _ = (Nat.choose r k : F) *
            ((-a) ^ (r - (n + k)) * (Nat.choose (r - k) n : F)) := by
            have : (r - k) - n = r - (n + k) := by
              simp [Nat.add_comm, Nat.sub_sub]
            simp [this]
      _ = (-a) ^ (r - (n + k)) *
            ((Nat.choose r k : F) * (Nat.choose (r - k) n : F)) := by
            ring
  have hscalar :
      (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) =
        (Nat.choose r k : F) * (Nat.choose (r - k) n : F) := by
    by_cases hnk : n + k ≤ r
    · have hsk : k ≤ n + k := Nat.le_add_left k n
      have h_nat :
          (Nat.choose r (n + k) * Nat.choose (n + k) k : ℕ) =
            Nat.choose r k * Nat.choose (r - k) n := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.choose_mul (n := r) (k := n + k) (s := k) hnk hsk)
      have h_natF :
          ((Nat.choose r (n + k) * Nat.choose (n + k) k : ℕ) : F) =
            (Nat.choose r k * Nat.choose (r - k) n : ℕ) := by
        exact congrArg (fun x : ℕ => (x : F)) h_nat
      have h_main :
          (Nat.choose r (n + k) : F) * (Nat.choose (n + k) k : F) =
            (Nat.choose r k : F) * (Nat.choose (r - k) n : F) := by
        simpa [Nat.cast_mul] using h_natF
      simpa [mul_comm] using h_main
    · have hlt : r < n + k := Nat.lt_of_not_ge hnk
      have hlt' : r - k < n :=
        (add_lt_add_iff_right (a := k)).1
          (by simpa [Nat.sub_add_cancel hk] using hlt)
      simp [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt hlt']
  have hmid :
      (-a) ^ (r - (n + k)) *
        (((n + k).choose k : F) * (Nat.choose r (n + k) : F)) =
      (-a) ^ (r - (n + k)) *
        ((Nat.choose r k : F) * (Nat.choose (r - k) n : F)) := by
    exact congrArg (fun x => (-a) ^ (r - (n + k)) * x) hscalar
  have hcoeff_eq :
      (hasseDerivOp F k ((Polynomial.X - Polynomial.C a) ^ r)).coeff n =
        (Polynomial.C (Nat.choose r k : F) *
          (Polynomial.X - Polynomial.C a) ^ (r - k)).coeff n :=
    (hL'.trans hmid).trans hR'.symm
  simpa using hcoeff_eq

lemma hasseDerivOp_prod_single_polynomial_dvd
    (F : Type*) [Field F] (k r : ℕ)
    (g : Polynomial F)
    (j : Fin r → Fin (k + 1))
    (h_sum : (Finset.univ : Finset (Fin r)).sum (fun i => (j i).val) = k) :
    g^(r - k) ∣
      (Finset.univ : Finset (Fin r)).prod
        (fun i => hasseDerivOp F (j i).val g) :=
by
  classical
  let s : Finset (Fin r) := Finset.univ
  let Z : Finset (Fin r) := s.filter fun i => (j i).val = 0
  let NZ : Finset (Fin r) := s.filter fun i => (j i).val ≠ 0
  have hZsum : Z.sum (fun i => (j i).val) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simpa [Z] using (Finset.mem_filter.1 hi).2
  have hsum_split :
      Z.sum (fun i => (j i).val) + NZ.sum (fun i => (j i).val) =
        s.sum (fun i => (j i).val) := by
    simpa [Z, NZ] using
      (Finset.sum_filter_add_sum_filter_not
        (s := s) (p := fun i : Fin r => (j i).val = 0) (f := fun i => (j i).val))
  have hNZsum : NZ.sum (fun i => (j i).val) = k := by
    have hs : s.sum (fun i => (j i).val) = k := by simpa [s] using h_sum
    have : Z.sum (fun i => (j i).val) + NZ.sum (fun i => (j i).val) = k := by
      simpa [hs] using hsum_split
    simpa [hZsum] using this
  have hNZ_card_le_sum : NZ.card ≤ NZ.sum (fun i => (j i).val) := by
    have hones_le :
        (∑ _x ∈ NZ, (1 : ℕ)) ≤ ∑ x ∈ NZ, (j x).val := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hne : (j i).val ≠ 0 := (Finset.mem_filter.1 hi).2
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
    calc
      NZ.card = ∑ _x ∈ NZ, (1 : ℕ) := (Finset.card_eq_sum_ones (s := NZ))
      _ ≤ ∑ x ∈ NZ, (j x).val := hones_le
  have hNZ_card_le_k : NZ.card ≤ k := by
    simpa [hNZsum] using hNZ_card_le_sum
  have hcard :
      Z.card + NZ.card = s.card := by
    simpa [Z, NZ] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := s) (p := fun i : Fin r => (j i).val = 0))
  have hZ_card_ge : r - k ≤ Z.card := by
    have hsum_le : Z.card + NZ.card ≤ Z.card + k :=
      Nat.add_le_add_left hNZ_card_le_k _
    have : (Z.card + NZ.card) - k ≤ (Z.card + k) - k :=
      Nat.sub_le_sub_right hsum_le _
    -- `s.card = r`
    simpa [s, hcard, Nat.add_sub_cancel_left] using this
  have hZprod :
      Z.prod (fun i => hasseDerivOp F (j i).val g) = g ^ Z.card := by
    calc
      Z.prod (fun i => hasseDerivOp F (j i).val g)
          = Z.prod (fun _ : Fin r => g) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              have : (j i).val = 0 := (Finset.mem_filter.1 hi).2
              simp [hasseDerivOp, this]
      _ = g ^ Z.card := by
            simpa using (Finset.prod_const (s := Z) (b := g))
  have hdiv_Z : g ^ (r - k) ∣ Z.prod (fun i => hasseDerivOp F (j i).val g) := by
    simpa [hZprod] using pow_dvd_pow g hZ_card_ge
  have hprod_split :
      Z.prod (fun i => hasseDerivOp F (j i).val g) *
        NZ.prod (fun i => hasseDerivOp F (j i).val g) =
        s.prod (fun i => hasseDerivOp F (j i).val g) := by
    simpa [Z, NZ] using
      (Finset.prod_filter_mul_prod_filter_not
        (s := s) (p := fun i : Fin r => (j i).val = 0)
        (f := fun i => hasseDerivOp F (j i).val g))
  have :=
    dvd_mul_of_dvd_left hdiv_Z (NZ.prod fun i => hasseDerivOp F (j i).val g)
  simpa [s, hprod_split] using this

lemma hasseDerivOp_pow_dvd
    (F : Type*) [Field F] (k r : ℕ) :
    ∀ g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (g^r) :=
by
  intro g
  have hLeib' := hasseLeibniz_general F k r (fun _ : Fin r => g)
  simp [Finset.card_univ, Fintype.card_fin] at hLeib'
  rw [hLeib']
  refine Finset.dvd_sum ?_
  intro j hj
  simpa using hasseDerivOp_prod_single_polynomial_dvd F k r g j (Finset.mem_filter.1 hj).2

lemma hasseDerivOp_mul_pow_dvd (F : Type*) [Field F]
    (k r : ℕ) :
    ∀ f g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (f * g^r) :=
by
  intro f g
  have :
      g ^ (r - k) ∣
        ∑ p ∈ Finset.antidiagonal k,
          hasseDerivOp F p.1 f * hasseDerivOp F p.2 (g ^ r) := by
    refine Finset.dvd_sum ?_
    intro p hp
    have : p.2 ≤ k := by
      have : p.2 ≤ p.1 + p.2 := Nat.le_add_left _ _
      simpa [Finset.mem_antidiagonal.1 hp] using this
    refine dvd_mul_of_dvd_right
      (dvd_trans (pow_dvd_pow _ (Nat.sub_le_sub_left this _))
        (hasseDerivOp_pow_dvd (F := F) (k := p.2) (r := r) g)) _
  simpa [hasseDerivOp,
    ← Polynomial.hasseDeriv_mul (R := F) (k := k) (f := f) (g := g ^ r)] using this

lemma hasse_formulas (F : Type*) [Field F] (k r : ℕ) (hk : k ≤ r) :
  (∀ a : F,
      hasseDerivOp F k ((Polynomial.X - Polynomial.C a)^r) =
        Polynomial.C (Nat.choose r k : F) * (Polynomial.X - Polynomial.C a)^(r - k))
  ∧
  (∀ f g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (f * g^r) ∧
      Polynomial.degree ((hasseDerivOp F k (f * g^r)) / (g^(r - k))) ≤
        (match (Polynomial.degree f + (k : WithBot ℕ) * Polynomial.degree g) with
         | ⊥ => ⊥
         | some n => some (n - k))) :=
by
  constructor
  · intro a
    simpa using
      (hasseDerivOp_X_sub_C_pow (F := F) (k := k) (r := r) (hk := hk) (a := a))
  · intro f g
    constructor
    · simpa using
        (hasseDerivOp_mul_pow_dvd (F := F) (k := k) (r := r) f g)
    · by_cases hf : f = 0
      · subst hf
        simp [hasseDerivOp]
      · by_cases hg : g = 0
        · subst hg
          by_cases hr0 : r = 0
          · subst hr0
            have hk0 : k = 0 := Nat.le_antisymm hk (Nat.zero_le _)
            subst hk0
            cases hdeg : (Polynomial.degree f) with
            | bot => simp [hdeg, hasseDerivOp]
            | coe a =>
                have : (↑a : WithBot ℕ) ≤ (some a : WithBot ℕ) := by
                  exact le_rfl
                simpa [hdeg, hasseDerivOp] using this
          · simp [hasseDerivOp, hr0]
        · -- Main case: `f ≠ 0` and `g ≠ 0`.
          classical
          set num : Polynomial F := hasseDerivOp F k (f * g ^ r)
          set den : Polynomial F := g ^ (r - k)
          have hdiv : den ∣ num := by
            simpa [num, den] using
              (hasseDerivOp_mul_pow_dvd (F := F) (k := k) (r := r) f g)
          have hden_ne : den ≠ 0 := by
            simpa [den] using pow_ne_zero (r - k) hg
          set q : Polynomial F := num / den
          by_cases hq0 : q = 0
          · simp [q, hq0]
          · have hq_ne : q ≠ 0 := hq0
            have hmul : den * q = num := by
              simpa [q] using
                (EuclideanDomain.mul_div_cancel'
                  (R := Polynomial F) (a := num) (b := den) hden_ne hdiv)
            have hnum_nat :
                num.natDegree ≤ f.natDegree + r * g.natDegree - k := by
              have h₁ :
                  num.natDegree ≤ (f * g ^ r).natDegree - k := by
                simpa [num, hasseDerivOp] using
                  (Polynomial.natDegree_hasseDeriv_le (p := f * g ^ r) (n := k))
              have h₂ : (f * g ^ r).natDegree ≤ f.natDegree + r * g.natDegree := by
                have hmul' :
                    (f * g ^ r).natDegree ≤ f.natDegree + (g ^ r).natDegree :=
                  Polynomial.natDegree_mul_le (p := f) (q := g ^ r)
                have hpow' : (g ^ r).natDegree ≤ r * g.natDegree :=
                  Polynomial.natDegree_pow_le (p := g) (n := r)
                exact hmul'.trans (Nat.add_le_add_left hpow' _)
              exact h₁.trans (Nat.sub_le_sub_right h₂ _)
            have hnum_nat_eq : num.natDegree = den.natDegree + q.natDegree := by
              have := congrArg Polynomial.natDegree hmul.symm
              simpa [Polynomial.natDegree_mul (p := den) (q := q) hden_ne hq_ne] using this
            have hden_nat : den.natDegree = (r - k) * g.natDegree := by
              simp [den, hg]
            have hq_nat :
                q.natDegree = num.natDegree - den.natDegree := by
              have : num.natDegree - den.natDegree = q.natDegree := by
                simpa [hnum_nat_eq] using
                  (Nat.add_sub_cancel_left den.natDegree q.natDegree)
              exact this.symm
            have hq_nat_le : q.natDegree ≤ f.natDegree + k * g.natDegree - k := by
              have hsub :
                  num.natDegree - den.natDegree ≤
                    (f.natDegree + r * g.natDegree - k) - den.natDegree :=
                Nat.sub_le_sub_right hnum_nat _
              have hr_mul :
                  r * g.natDegree =
                    k * g.natDegree + (r - k) * g.natDegree := by
                calc
                  r * g.natDegree = (k + (r - k)) * g.natDegree := by
                    simp [Nat.add_sub_of_le hk]
                  _ = k * g.natDegree + (r - k) * g.natDegree := by
                    simp [Nat.add_mul]
              have hRHS :
                  (f.natDegree + r * g.natDegree - k) - den.natDegree =
                    f.natDegree + k * g.natDegree - k := by
                calc
                  (f.natDegree + r * g.natDegree - k) - den.natDegree
                      = f.natDegree + r * g.natDegree - (k + den.natDegree) := by
                          simpa [Nat.sub_sub]
                  _ = f.natDegree + (k * g.natDegree + den.natDegree) - (k + den.natDegree) := by
                        simp [hr_mul, hden_nat, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                  _ = f.natDegree + k * g.natDegree - k := by
                        calc
                          f.natDegree + (k * g.natDegree + den.natDegree) - (k + den.natDegree)
                              = (f.natDegree + k * g.natDegree + den.natDegree) - (k + den.natDegree) := by
                                  simp [Nat.add_assoc]
                          _ = (f.natDegree + k * g.natDegree) - k := by
                                simpa [Nat.add_assoc] using
                                  (Nat.add_sub_add_right (f.natDegree + k * g.natDegree) den.natDegree k)
                          _ = f.natDegree + k * g.natDegree - k := rfl
              have : q.natDegree ≤ (f.natDegree + r * g.natDegree - k) - den.natDegree := by
                simpa [hq_nat] using hsub
              simpa [hRHS] using this
            have hdeg_q :
                Polynomial.degree q ≤
                  ((f.natDegree + k * g.natDegree - k : ℕ) : WithBot ℕ) :=
              (Polynomial.natDegree_le_iff_degree_le).1 hq_nat_le
            simpa [q, Polynomial.degree_eq_natDegree hf, Polynomial.degree_eq_natDegree hg] using
              hdeg_q

lemma hasse_divisibility (F : Type*) [Field F] (f : Polynomial F) (a : F) (ℓ : ℕ)
    (hvan : ∀ k < ℓ, (hasseDerivOp F k f).eval a = 0) :
    (Polynomial.X - Polynomial.C a)^ℓ ∣ f :=
by
  set t : Polynomial F := Polynomial.taylor a f
  have hcoeff0 : ∀ k < ℓ, t.coeff k = 0 := by
    intro k hk
    simpa [t, Polynomial.taylor_coeff, hasseDerivOp] using hvan k hk
  have hfact :
      t.sum (fun i c => Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ i) =
        (Polynomial.X - Polynomial.C a) ^ ℓ *
          t.sum (fun i c =>
            Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ (i - ℓ)) := by
    simp [Polynomial.sum_def, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hle : ℓ ≤ i := by
      by_contra h
      have : t.coeff i = 0 := hcoeff0 i (Nat.lt_of_not_ge h)
      exact (Polynomial.mem_support_iff.mp hi) this
    calc
      Polynomial.C (t.coeff i) * (Polynomial.X - Polynomial.C a) ^ i
          = (Polynomial.X - Polynomial.C a) ^ i *
              Polynomial.C (t.coeff i) := by
                simp [mul_comm]
      _ = (Polynomial.X - Polynomial.C a) ^ (ℓ + (i - ℓ)) *
              Polynomial.C (t.coeff i) := by
                simp [Nat.add_sub_of_le hle]
      _ = (Polynomial.X - Polynomial.C a) ^ ℓ *
              (Polynomial.C (t.coeff i) *
                (Polynomial.X - Polynomial.C a) ^ (i - ℓ)) := by
                simp [pow_add, mul_comm, mul_assoc]
  refine ⟨t.sum (fun i c => Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ (i - ℓ)), ?_⟩
  have hf :
      f =
        t.sum (fun i c => Polynomial.C c * (Polynomial.X - Polynomial.C a) ^ i) := by
    simpa [t] using (Polynomial.sum_taylor_eq (R := F) f a).symm
  exact hf.trans hfact
