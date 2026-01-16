import Mathlib

noncomputable def hasseDerivOp (F : Type*) [Field F] (k : ℕ) : Polynomial F → Polynomial F :=
  fun p => (Polynomial.hasseDeriv k) p

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
  let s : Finset (Fin r) := Finset.univ
  let Z : Finset (Fin r) := s.filter fun i => (j i).val = 0
  let NZ : Finset (Fin r) := s.filter fun i => (j i).val ≠ 0
  have hprod_split :
      Z.prod (fun i => hasseDerivOp F (j i).val g) *
        NZ.prod (fun i => hasseDerivOp F (j i).val g) =
      s.prod (fun i => hasseDerivOp F (j i).val g) :=
    Finset.prod_filter_mul_prod_filter_not
      (s := s)
      (p := fun i : Fin r => (j i).val = 0)
      (f := fun i => hasseDerivOp F (j i).val g)
  have hsum_decomp :
      Z.sum (fun i => (j i).val) + NZ.sum (fun i => (j i).val) =
        s.sum (fun i => (j i).val) :=
    Finset.sum_filter_add_sum_filter_not
      (s := s)
      (p := fun i : Fin r => (j i).val = 0)
      (f := fun i => (j i).val)
  have hZsum_zero :
      Z.sum (fun i => (j i).val) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simpa using (Finset.mem_filter.1 hi).2
  have hsum_NZ :
      NZ.sum (fun i => (j i).val) = k := by
    simpa [hZsum_zero] using hsum_decomp.trans h_sum
  have h_le_Zcard : r - k ≤ Z.card := by
    have hNZ_card_le_sum :
        NZ.card ≤ NZ.sum (fun i => (j i).val) := by
      have hones :
          NZ.card = NZ.sum (fun _ : Fin r => (1 : ℕ)) :=
        Finset.card_eq_sum_ones (s := NZ)
      have hterm :
          NZ.sum (fun _ : Fin r => (1 : ℕ)) ≤
            NZ.sum (fun i => (j i).val) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        obtain ⟨_, hne⟩ := Finset.mem_filter.1 hi
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
      rwa [hones.symm] at hterm
    have hNZ_card_le_k : NZ.card ≤ k := by
      simpa [hsum_NZ] using hNZ_card_le_sum
    have h_r_eq : r = Z.card + NZ.card := by
      have hcard_Z_NZ :
          Z.card + NZ.card = s.card :=
        Finset.filter_card_add_filter_neg_card_eq_card
          (s := s)
          (p := fun i : Fin r => (j i).val = 0)
      simpa [s] using hcard_Z_NZ.symm
    simpa [h_r_eq, Nat.add_comm] using
      Nat.sub_le_sub_left hNZ_card_le_k r
  have hZprod :
      Z.prod (fun i => hasseDerivOp F (j i).val g) = g ^ Z.card := by
    calc
      Z.prod (fun i => hasseDerivOp F (j i).val g)
          = Z.prod (fun _ : Fin r => g) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              obtain ⟨_, hzero⟩ := Finset.mem_filter.1 hi
              simp [hasseDerivOp, hzero]
      _ = g ^ Z.card :=
        Finset.prod_const (s := Z) (b := g)
  have hdiv_Z :
      g ^ (r - k) ∣ Z.prod (fun i => hasseDerivOp F (j i).val g) := by
    simpa [hZprod] using pow_dvd_pow g h_le_Zcard
  have :=
    dvd_mul_of_dvd_left hdiv_Z
      (NZ.prod fun i => hasseDerivOp F (j i).val g)
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
            have :
                Polynomial.degree f ≤
                  (match Polynomial.degree f with
                   | ⊥ => (⊥ : WithBot ℕ)
                   | some n => some (n - 0)) := by
              cases hdeg : Polynomial.degree f with
              | bot =>
                  simp
              | coe a =>
                  have : ((↑a : WithBot ℕ)) ≤ some a := le_rfl
                  simpa [hdeg] using this
            simpa [hasseDerivOp] using this
          · simp [hasseDerivOp, hr0]
        · -- Main case: `f ≠ 0` and `g ≠ 0`.
          set num : Polynomial F := hasseDerivOp F k (f * g ^ r) with hnum
          set den : Polynomial F := g ^ (r - k) with hden
          have hdiv : den ∣ num := by
            have hdiv' : g ^ (r - k) ∣ hasseDerivOp F k (f * g ^ r) :=
              hasseDerivOp_mul_pow_dvd (F := F) (k := k) (r := r) f g
            simpa [hnum, hden] using hdiv'
          have hden_ne : den ≠ 0 := by
            have hg0 : g ≠ 0 := hg
            simpa [hden] using pow_ne_zero (r - k) hg0
          set q : Polynomial F := num / den with hq_def
          have h_deg_q :
              Polynomial.degree q ≤
                (match
                    Polynomial.degree f
                      + (k : WithBot ℕ) * Polynomial.degree g with
                 | ⊥ => (⊥ : WithBot ℕ)
                 | some n => some (n - k)) := by
            by_cases hq0 : q = 0
            · simp [hq0]
            · have hq_ne : q ≠ 0 := hq0
              have hnum_nat_le1 :
                  num.natDegree ≤ (f * g ^ r).natDegree - k := by
                simpa [hnum, hasseDerivOp] using
                  (Polynomial.natDegree_hasseDeriv_le (p := f * g ^ r) (n := k))
              have hmul_nat_le :
                  (f * g ^ r).natDegree ≤
                    f.natDegree + (g ^ r).natDegree :=
                Polynomial.natDegree_mul_le (p := f) (q := g ^ r)
              have hpow_nat_le :
                  (g ^ r).natDegree ≤ r * g.natDegree :=
                Polynomial.natDegree_pow_le (p := g) (n := r)
              have hfg_nat_le :
                  (f * g ^ r).natDegree ≤
                    f.natDegree + r * g.natDegree :=
                le_trans hmul_nat_le (Nat.add_le_add_left hpow_nat_le _)
              have hnum_nat_le :
                  num.natDegree ≤ f.natDegree + r * g.natDegree - k :=
                le_trans hnum_nat_le1 (Nat.sub_le_sub_right hfg_nat_le _)
              have hmul_eq : den * q = num := by
                simpa [hq_def] using
                  (EuclideanDomain.mul_div_cancel'
                    (R := Polynomial F) (a := num) (b := den) hden_ne hdiv)
              have hnum_nat_eq :
                  num.natDegree = den.natDegree + q.natDegree := by
                have := congrArg Polynomial.natDegree hmul_eq.symm
                simpa [Polynomial.natDegree_mul (p := den) (q := q) hden_ne hq_ne] using this
              have hden_nat : den.natDegree = (r - k) * g.natDegree := by
                simp [hden]
              have hsub_le :
                  num.natDegree - (r - k) * g.natDegree ≤
                    f.natDegree + r * g.natDegree - k
                      - (r - k) * g.natDegree :=
                Nat.sub_le_sub_right hnum_nat_le _
              have hq_eq :
                  num.natDegree - (r - k) * g.natDegree =
                    q.natDegree := by
                have : num.natDegree =
                    (r - k) * g.natDegree + q.natDegree := by
                  simpa [hden_nat, Nat.add_comm] using hnum_nat_eq
                simp [this]
              have hr : k + (r - k) = r := Nat.add_sub_of_le hk
              have hr_mul :
                  r * g.natDegree =
                    k * g.natDegree + (r - k) * g.natDegree := by
                calc
                  r * g.natDegree
                      = (k + (r - k)) * g.natDegree := by simp [hr]
                  _ = k * g.natDegree + (r - k) * g.natDegree := by
                        simp [Nat.add_mul]
              have hRHS_eq :
                  f.natDegree + r * g.natDegree - k
                      - (r - k) * g.natDegree =
                    f.natDegree + k * g.natDegree - k := by
                have h1 :
                    f.natDegree + r * g.natDegree - k
                        - (r - k) * g.natDegree =
                      f.natDegree + r * g.natDegree
                        - (k + (r - k) * g.natDegree) := by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                      (tsub_add_eq_tsub_tsub
                        (a := f.natDegree + r * g.natDegree)
                        (b := k)
                        (c := (r - k) * g.natDegree)).symm
                have h2 :
                    f.natDegree + r * g.natDegree
                        - (k + (r - k) * g.natDegree) =
                      f.natDegree + k * g.natDegree - k := by
                  calc
                    f.natDegree + r * g.natDegree
                        - (k + (r - k) * g.natDegree)
                        = f.natDegree
                            + (k * g.natDegree + (r - k) * g.natDegree)
                            - (k + (r - k) * g.natDegree) := by
                            simp [hr_mul]
                    _ = f.natDegree + k * g.natDegree
                          + (r - k) * g.natDegree
                          - (k + (r - k) * g.natDegree) := by
                          simp [Nat.add_assoc]
                    _ = f.natDegree + k * g.natDegree - k := by
                      simpa [Nat.add_comm, Nat.add_left_comm,
                        Nat.add_assoc] using
                        (add_tsub_add_eq_tsub_right
                          (a := f.natDegree + k * g.natDegree)
                          (c := (r - k) * g.natDegree)
                          (b := k))
                exact h1.trans h2
              have hq_nat_le :
                  q.natDegree ≤ f.natDegree + k * g.natDegree - k := by
                have := hsub_le
                simpa [hq_eq, hRHS_eq] using this
              have hdeg_q' :
                  Polynomial.degree q ≤
                    ((f.natDegree + k * g.natDegree - k : ℕ) :
                      WithBot ℕ) :=
                (Polynomial.natDegree_le_iff_degree_le).1 hq_nat_le
              have hf_deg :
                  Polynomial.degree f =
                    (Polynomial.natDegree f : WithBot ℕ) :=
                Polynomial.degree_eq_natDegree hf
              have hg_deg :
                  Polynomial.degree g =
                    (Polynomial.natDegree g : WithBot ℕ) :=
                Polynomial.degree_eq_natDegree hg
              simpa [hf_deg, hg_deg] using hdeg_q'
          simpa [hnum, hden, hq_def] using h_deg_q

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
