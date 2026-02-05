import Mathlib
import RiemannHypothesisCurves.Utils
import RiemannHypothesisCurves.StepanovVanishing

lemma stepanov_sigma_degree_bound_fin
    (F : Type*) [Field F]
    (d k m J : ℕ) (a : F)
    (rjk sjk : Fin J → Polynomial F)
    (hdeg_r : ∀ j : Fin J, (rjk j).natDegree ≤ d + k * (m - 1))
    (hdeg_s : ∀ j : Fin J, (sjk j).natDegree ≤ d + k * (m - 1)) :
    (∑ j : Fin J, (rjk j + Polynomial.C a * sjk j) * Polynomial.X ^ (j : ℕ)).natDegree
      ≤ J - 1 + d + k * (m - 1) :=
by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  have h_sum : (rjk j + Polynomial.C a * sjk j).natDegree ≤ d + k * (m - 1) := by
    simpa [hdeg_s j] using
      (Polynomial.natDegree_add_le (rjk j) (Polynomial.C a * sjk j)).trans
        (max_le_max (hdeg_r j) (Polynomial.natDegree_C_mul_le a _))
  have hmul :
      ((rjk j + Polynomial.C a * sjk j) * Polynomial.X ^ (j : ℕ)).natDegree ≤
        (rjk j + Polynomial.C a * sjk j).natDegree + (j : ℕ) := by
    simpa [Polynomial.natDegree_X_pow] using
      (Polynomial.natDegree_mul_le
        (p := rjk j + Polynomial.C a * sjk j) (q := (Polynomial.X : Polynomial F) ^ (j : ℕ)))
  calc
    ((rjk j + Polynomial.C a * sjk j) * Polynomial.X ^ (j : ℕ)).natDegree
        ≤ (rjk j + Polynomial.C a * sjk j).natDegree + (j : ℕ) := hmul
    _ ≤ d + k * (m - 1) + (j : ℕ) :=
      Nat.add_le_add_right h_sum _
    _ ≤ J - 1 + d + k * (m - 1) := by
      have := add_le_add_left (Nat.le_pred_of_lt j.isLt) (d + k * (m - 1))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

lemma stepanov_system_constraint_count
    (ℓ J d m q : ℕ) (B : ℕ)
    (hℓ_pos : 0 < ℓ) (hm_ge_two : 2 ≤ m)
    (hq6m : 6 * m < q)
    (_hℓ : ℓ ≤ q / 3)
    (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
    (_hJ : 1 ≤ J)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1))) :
    B ≤ ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 ∧
    (B : ℝ) <
      (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
        (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) :=
by
  have h_sum :
      ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
        ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
    have h_mul_div :
        (ℓ * (ℓ - 1) / 2) * (m - 1) =
          ℓ * (ℓ - 1) * (m - 1) / 2 := by
      have h2 : 2 ∣ ℓ * (ℓ - 1) := (Nat.even_mul_pred_self ℓ).two_dvd
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        (Nat.mul_div_right_comm h2 (m - 1)).symm
    have h_lin :
        ∑ k ∈ Finset.range ℓ, k * (m - 1) =
          (∑ k ∈ Finset.range ℓ, k) * (m - 1) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        (Finset.sum_mul (s := Finset.range ℓ)
          (f := fun k : ℕ => k) (a := m - 1)).symm
    calc
      ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) =
          ∑ k ∈ Finset.range ℓ, ((J + d) + k * (m - 1)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [add_assoc]
      _ = (∑ k ∈ Finset.range ℓ, (J + d)) +
            ∑ k ∈ Finset.range ℓ, k * (m - 1) := by
            simp [Finset.sum_add_distrib]
      _ = ℓ * (J + d) + (∑ k ∈ Finset.range ℓ, k) * (m - 1) := by
            simp [Finset.sum_const, Finset.card_range, h_lin]
      _ = ℓ * (J + d) + (ℓ * (ℓ - 1) / 2) * (m - 1) := by
            simp [Finset.sum_range_id]
      _ = ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
            simp [Nat.mul_add, Nat.add_assoc, h_mul_div]
  have hB_nat :
      B ≤ ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 := by
    simpa [h_sum] using hB
  have hB_real_le :
      (B : ℝ) ≤
        ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast hB_nat
  have hx_pos : (0 : ℚ) < ((q : ℚ) - m) / 2 := by
    have hm_lt_q : m < q := by
      exact lt_of_le_of_lt (Nat.le_mul_of_pos_left m (by decide : 0 < 6)) hq6m
    have : (m : ℚ) < (q : ℚ) := by exact_mod_cast hm_lt_q
    exact div_pos (sub_pos.mpr this) (by norm_num)
  have hd_lt_rat : (d : ℚ) < ((q : ℚ) - m) / 2 :=
    Nat.lt_ceil.mp <| Nat.lt_of_le_pred (Nat.ceil_pos.mpr hx_pos) (by simp [hd])
  have hd_lt_real : (d : ℝ) < ((q : ℝ) - (m : ℝ)) / 2 := by
    exact_mod_cast hd_lt_rat
  have hEd_lt :
      (ℓ : ℝ) * (d : ℝ) <
        (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) :=
    mul_lt_mul_of_pos_left hd_lt_real (by exact_mod_cast hℓ_pos)
  have hS_cast :
      ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) =
        (ℓ : ℝ) * (J : ℝ) + (ℓ : ℝ) * (d : ℝ) +
          ((ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) := by
    simp [Nat.cast_add, Nat.cast_mul, add_assoc]
  have h_div_le :
      ((ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) ≤
        ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 := by
    simpa [Nat.cast_mul, mul_assoc, div_eq_mul_inv] using
      (Nat.cast_div_le (α := ℝ)
        (m := ℓ * (ℓ - 1) * (m - 1)) (n := 2))
  have hℓ_sub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    have hℓ_ge1 : 1 ≤ ℓ := Nat.succ_le_of_lt hℓ_pos
    simpa using (Nat.cast_sub (R := ℝ) hℓ_ge1)
  have hm_sub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have hm_ge1 : 1 ≤ m :=
      le_trans (show (1 : ℕ) ≤ 2 by decide) hm_ge_two
    simpa using (Nat.cast_sub (R := ℝ) hm_ge1)
  have hCf_eq :
      ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 =
        (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 := by
    simp [hℓ_sub, hm_sub, mul_assoc]
  have hS_le_target1 :
      ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) ≤
        (ℓ : ℝ) * (J : ℝ) + (ℓ : ℝ) * (d : ℝ) +
          (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 := by
    have h' :=
      add_le_add_left
        (add_le_add_left h_div_le ((ℓ : ℝ) * (d : ℝ)))
        ((ℓ : ℝ) * (J : ℝ))
    simpa [hS_cast, hCf_eq, add_assoc, add_comm, add_left_comm] using h'
  have hAEC_lt :
      (ℓ : ℝ) * (J : ℝ) + (ℓ : ℝ) * (d : ℝ) +
          (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 <
        (ℓ : ℝ) * (J : ℝ) +
          (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) +
          (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 := by
    exact
      add_lt_add_right
        (add_lt_add_left hEd_lt ((ℓ : ℝ) * (J : ℝ))) _
  have hS_lt_target :
      ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) <
        (ℓ : ℝ) *
          ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
            (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) := by
    have h' :
        ((ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 : ℕ) : ℝ) <
          (ℓ : ℝ) * (J : ℝ) +
            (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 :=
      lt_of_le_of_lt hS_le_target1 hAEC_lt
    have h_target_eq :
        (ℓ : ℝ) * (J : ℝ) +
            (ℓ : ℝ) * (((q : ℝ) - (m : ℝ)) / 2) +
            (ℓ : ℝ) * (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 =
          (ℓ : ℝ) *
            ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
              (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) := by
      ring
    simpa [h_target_eq] using h'
  have hB_lt :
      (B : ℝ) <
        (ℓ : ℝ) *
          ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
            (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) :=
    lt_of_le_of_lt hB_real_le hS_lt_target
  exact ⟨hB_nat, hB_lt⟩

lemma stepanov_monotone_in_J
    {J₁ J₂ D ℓ x C : ℝ}
    (hA : 2 * J₁ * D > ℓ * (J₁ + x) + C)
    (hD_nonneg : 0 ≤ 2 * D - ℓ)
    (hJmono : J₁ ≤ J₂) :
  2 * J₂ * D > ℓ * (J₂ + x) + C :=
by
  have hdiff :
      0 ≤ (2 * J₂ * D - ℓ * (J₂ + x)) - (2 * J₁ * D - ℓ * (J₁ + x)) := by
    have h : 0 ≤ (J₂ - J₁) * (2 * D - ℓ) :=
      mul_nonneg (sub_nonneg.mpr hJmono) hD_nonneg
    have :
        (2 * J₂ * D - ℓ * (J₂ + x)) - (2 * J₁ * D - ℓ * (J₁ + x)) =
          (J₂ - J₁) * (2 * D - ℓ) := by
      ring
    simpa [this] using h
  have hmono :
      2 * J₁ * D - ℓ * (J₁ + x) ≤ 2 * J₂ * D - ℓ * (J₂ + x) := by
    linarith [hdiff]
  have hA' : C < 2 * J₁ * D - ℓ * (J₁ + x) := by
    linarith [hA]
  have hA'' : C < 2 * J₂ * D - ℓ * (J₂ + x) :=
    lt_of_lt_of_le hA' hmono
  linarith [hA'']

lemma stepanov_twoD_sub_ell_pos
    (q m ℓ : ℕ) (hq6m : q > 6 * m) (hℓ : ℓ ≤ q / 3) :
  0 < 2 * (Int.ceil (((q : ℝ) - (m : ℝ)) / 2) : ℝ) - (ℓ : ℝ) :=
by
  have hm_lt_qdiv6 : (m : ℝ) < (q : ℝ) / 6 :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < (6 : ℝ))).mpr <|
      by
        have h : (6 : ℝ) * (m : ℝ) < (q : ℝ) := by
          exact_mod_cast (by simpa [Nat.mul_comm] using hq6m : 6 * m < q)
        simpa [mul_comm] using h
  have hℓ_le_qdiv3 : (ℓ : ℝ) ≤ (q : ℝ) / 3 := by
    exact natCast_le_div ℓ q 3 hℓ
  set x : ℝ := ((q : ℝ) - (m : ℝ)) / 2 with hx
  have h_lt : (ℓ : ℝ) < 2 * (Int.ceil x : ℝ) := by
    have h_ell_lt_qm : (ℓ : ℝ) < (q : ℝ) - (m : ℝ) := by
      have h : (q : ℝ) / 2 < (q : ℝ) - (m : ℝ) - (ℓ : ℝ) := by
        nlinarith [hm_lt_qdiv6, hℓ_le_qdiv3]
      nlinarith [h]
    have h_qm_le : (q : ℝ) - (m : ℝ) ≤ 2 * (Int.ceil x : ℝ) := by
      have hx_two : (2 : ℝ) * x = (q : ℝ) - (m : ℝ) := by
        have : x + x = (q : ℝ) - (m : ℝ) := by simp [hx, add_halves]
        simpa [two_mul] using this
      have := (mul_le_mul_of_nonneg_left (Int.le_ceil x) (by norm_num) :
        (2 : ℝ) * x ≤ (2 : ℝ) * (Int.ceil x : ℝ))
      simpa [hx_two] using this
    exact lt_of_lt_of_le h_ell_lt_qm h_qm_le
  exact sub_pos.mpr (by simpa [hx] using h_lt)

lemma stepanov_system_dimension_inequality_nat
    (q m ℓ : ℕ)
    (hm_ge_two : 2 ≤ m) (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
    (hℓ_pos : 0 < ℓ)
    (B : ℕ)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ,
      (Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) +
        (Nat.ceil (((q : ℚ) - m) / 2) - 1) + k * (m - 1))) :
    let J := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
    2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B :=
by
  intro J
  -- basic integer setup
  set d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1 with hd
  have hB_le : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) := by
    simpa [J, hd, add_comm, add_left_comm, add_assoc] using hB
  have hq6m_nat : 6 * m < q := by simpa [Nat.mul_comm] using hq6m
  have hq_pos_nat : 0 < q := lt_of_le_of_lt (Nat.zero_le (6 * m)) hq6m_nat
  have hm_lt_q : m < q :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left m (by decide : 0 < 6)) hq6m_nat
  -- positivity of the expression defining J
  have hJ_expr_pos :
      0 < ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) := by
    have hℓ_posℚ : (0 : ℚ) < (ℓ : ℚ) := by exact_mod_cast hℓ_pos
    have hq_posℚ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq_pos_nat
    have hm_nonnegℚ : (0 : ℚ) ≤ (m : ℚ) := by exact_mod_cast (Nat.zero_le m)
    positivity
  have hJ_pos : 1 ≤ J :=
    (Nat.one_le_ceil_iff
      (a := ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)))).2
      hJ_expr_pos
  -- apply constraint-count inequality and simplify its RHS a bit
  have hB_real_small :
      (B : ℝ) <
        (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
          (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) :=
    (stepanov_system_constraint_count ℓ J d m q B
      hℓ_pos hm_ge_two hq6m_nat hl hd hJ_pos hB_le).2
  -- some simple arithmetic bounds
  have hℓ_nonneg : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Nat.zero_le ℓ)
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm_ge_two
  have hm1_nonneg : 0 ≤ (m : ℝ) - 1 :=
    sub_nonneg.mpr (by
      exact_mod_cast (le_trans (show (1 : ℕ) ≤ 2 by decide) hm_ge_two))
  have hB_lt_Bmax_J :
      (B : ℝ) <
        (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2) +
          (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 :=
    by
      refine lt_of_lt_of_le hB_real_small ?_
      have hℓ' : (ℓ : ℝ) - 1 ≤ (ℓ : ℝ) := by linarith
      have hmul :
          ((ℓ : ℝ) - 1) * ((m : ℝ) - 1) ≤ (ℓ : ℝ) * ((m : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hℓ' hm1_nonneg
      have hdiv :
          (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2 ≤
            (ℓ : ℝ) * ((m : ℝ) - 1) / 2 :=
        div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 2)
      have hterm :
          (ℓ : ℝ) * ((((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) ≤
            (ℓ : ℝ) * ((ℓ : ℝ) * ((m : ℝ) - 1) / 2) :=
        mul_le_mul_of_nonneg_left hdiv hℓ_nonneg
      have hsum :=
        add_le_add_left hterm ((ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2))
      simpa [mul_add, add_assoc, pow_two, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
        hsum
  -- switch to a more convenient notation over ℝ
  set Jreal : ℝ :=
      (ℓ : ℝ) / 2 + ((ℓ : ℝ) ^ 2 * (m : ℝ)) / (q : ℝ) with hJreal_def
  set xR : ℝ := ((q : ℝ) - (m : ℝ)) / 2 with hxR_def
  set D : ℝ := (Int.ceil xR : ℝ) with hD_def
  set C : ℝ := (ℓ : ℝ) ^ 2 * ((m : ℝ) - 1) / 2 with hC_def
  -- nonnegativity of 2D − ℓ
  have hD_nonneg : 0 ≤ 2 * D - (ℓ : ℝ) := by
    have hpos := stepanov_twoD_sub_ell_pos q m ℓ hq6m hl
    have : 0 < 2 * (Int.ceil xR : ℝ) - (ℓ : ℝ) := by
      simpa [xR, hxR_def, D, hD_def] using hpos
    exact le_of_lt this
  -- relate Jreal and J (ceil over ℚ vs ℝ)
  set tQ : ℚ :=
      (ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ) with htQ_def
  have htQ_le_ceil : (tQ : ℚ) ≤ Nat.ceil tQ := Nat.le_ceil tQ
  have hJreal_le_J : Jreal ≤ (J : ℝ) := by
    have : (tQ : ℝ) ≤ (Nat.ceil tQ : ℝ) := by exact_mod_cast htQ_le_ceil
    simpa [Jreal, tQ, hJreal_def, htQ_def] using this
  -- define A_real and Bmax_real
  set A_real : ℝ := 2 * Jreal * D with hAreal_def
  set Bmax_real : ℝ :=
      (ℓ : ℝ) * (Jreal + xR) + C with hBmax_def
  -- lower bound on A_real
  have hA_ge : Jreal * ((q : ℝ) - (m : ℝ)) ≤ A_real := by
    have hx_le_ceil : xR ≤ (Int.ceil xR : ℝ) := Int.le_ceil xR
    have hJreal_nonneg : (0 : ℝ) ≤ Jreal := by
      have h1 : (0 : ℝ) ≤ (ℓ : ℝ) / 2 :=
        div_nonneg hℓ_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      have h2 :
          (0 : ℝ) ≤ ((ℓ : ℝ) ^ 2 * (m : ℝ)) / (q : ℝ) := by
        have hnum : (0 : ℝ) ≤ (ℓ : ℝ) ^ 2 * (m : ℝ) :=
          mul_nonneg (pow_two_nonneg _) (by exact_mod_cast (Nat.zero_le m))
        have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos_nat
        exact div_nonneg hnum (le_of_lt hq_pos)
      have := add_nonneg h1 h2
      simpa [Jreal, hJreal_def] using this
    have h2J_nonneg : (0 : ℝ) ≤ 2 * Jreal :=
      mul_nonneg (by norm_num) hJreal_nonneg
    have hmul :
        (2 * Jreal) * xR ≤
          (2 * Jreal) * (Int.ceil xR : ℝ) :=
      mul_le_mul_of_nonneg_left hx_le_ceil h2J_nonneg
    have hx_two : (2 : ℝ) * xR = (q : ℝ) - (m : ℝ) := by
      have : xR + xR = (q : ℝ) - (m : ℝ) := by
        simp [xR, add_halves]
      simpa [two_mul] using this
    have hA_left :
        (2 * Jreal) * xR = Jreal * ((q : ℝ) - (m : ℝ)) := by
      calc
        (2 * Jreal) * xR = Jreal * (2 * xR) := by ac_rfl
        _ = Jreal * ((q : ℝ) - (m : ℝ)) := by simp [hx_two]
    have hA_eq :
        (2 * Jreal) * (Int.ceil xR : ℝ) = A_real := by
      simp [A_real, hAreal_def, D]
    have hA_aux : (2 * Jreal) * xR ≤ A_real := by
      simpa [hA_eq] using hmul
    simpa [hA_left] using hA_aux
  -- key inequality Jreal*(q-m) > Bmax_real
  have hJ_gt_Bmax : Bmax_real < Jreal * ((q : ℝ) - (m : ℝ)) := by
    -- first rewrite the difference in a more symmetric way
    have hD_eq :
        Jreal * ((q : ℝ) - (m : ℝ)) - Bmax_real =
          (Jreal - (ℓ : ℝ) / 2) *
              ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
            (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
      simp [Bmax_real, hxR_def, hC_def]
      ring_nf
    have h_eqJ :
        Jreal - (ℓ : ℝ) / 2 =
          (ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ) := by
      simp [Jreal, sub_eq_add_neg, add_comm, add_assoc]
    have hJ_minus_pos : 0 < Jreal - (ℓ : ℝ) / 2 := by
      have hℓ_posR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
      have hm_posR : 0 < (m : ℝ) := by exact_mod_cast hm_pos
      have hq_posR : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
      have : 0 < (ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ) := by
        positivity
      simpa [h_eqJ] using this
    -- obtain that q/2 < q − m − ℓ
    have hq6m_real : (6 : ℝ) * (m : ℝ) < (q : ℝ) := by exact_mod_cast hq6m_nat
    have hm_lt_qdiv6 : (m : ℝ) < (q : ℝ) / 6 := by
      have h6pos : (0 : ℝ) < (6 : ℝ) := by norm_num
      have : (m : ℝ) * 6 < (q : ℝ) := by
        simpa [mul_comm] using hq6m_real
      exact (lt_div_iff₀ h6pos).mpr this
    have hℓ_le_qdiv3 : (ℓ : ℝ) ≤ (q : ℝ) / 3 := by
      exact natCast_le_div ℓ q 3 hl
    have h_qmℓ_gt :
        (q : ℝ) / 2 < (q : ℝ) - (m : ℝ) - (ℓ : ℝ) := by
      nlinarith [hm_lt_qdiv6, hℓ_le_qdiv3]
    -- compare two products using the previous inequality
    have h_prod_gt :
        (Jreal - (ℓ : ℝ) / 2) *
            ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) >
          (Jreal - (ℓ : ℝ) / 2) * ((q : ℝ) / 2) :=
      mul_lt_mul_of_pos_left h_qmℓ_gt hJ_minus_pos
    have h_prod_eq :
        (Jreal - (ℓ : ℝ) / 2) * ((q : ℝ) / 2) =
          (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
      have hq_ne : (q : ℝ) ≠ 0 := by
        have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos_nat
        exact ne_of_gt hq_pos
      have :
          ((ℓ : ℝ) ^ 2 * (m : ℝ) / (q : ℝ)) * ((q : ℝ) / 2) =
            (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
        field_simp [hq_ne]
      simpa [h_eqJ] using this
    have hmain :
        (Jreal - (ℓ : ℝ) / 2) *
            ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) >
          (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 := by
      simpa [h_prod_eq] using h_prod_gt
    have hD_pos :
        Jreal * ((q : ℝ) - (m : ℝ)) - Bmax_real > 0 := by
      have hD2_pos :
          (Jreal - (ℓ : ℝ) / 2) *
              ((q : ℝ) - (m : ℝ) - (ℓ : ℝ)) -
            (ℓ : ℝ) ^ 2 * (m : ℝ) / 2 > 0 :=
        sub_pos.mpr hmain
      simpa [hD_eq] using hD2_pos
    exact sub_pos.mp hD_pos
  -- combine to get Bmax_real < A_real
  have hA_gt_Bmax : Bmax_real < A_real :=
    lt_of_lt_of_le hJ_gt_Bmax hA_ge
  -- monotonicity in J
  have hA_gt_Bmax_J :
      2 * (J : ℝ) * D >
        (ℓ : ℝ) * ((J : ℝ) + xR) + C :=
    stepanov_monotone_in_J (J₁ := Jreal) (J₂ := (J : ℝ)) (D := D)
      (ℓ := (ℓ : ℝ)) (x := xR) (C := C)
      (by
        have :
            (ℓ : ℝ) * (Jreal + xR) + C <
              2 * Jreal * D := by
          simpa [A_real, hAreal_def, Bmax_real, hBmax_def] using hA_gt_Bmax
        simpa using this)
      (by simpa [D, hD_def] using hD_nonneg)
      hJreal_le_J
  have hB_lt_A_real :
      (B : ℝ) < 2 * (J : ℝ) * D :=
    lt_of_lt_of_le hB_lt_Bmax_J (le_of_lt hA_gt_Bmax_J)
  -- convert the statement back to ℚ / ℕ
  set xQ : ℚ := ((q : ℚ) - m) / 2 with hxQ_def
  have hxQ_nonneg : 0 ≤ xQ := by
    have hsub_nonneg : 0 ≤ (q : ℚ) - m :=
      sub_nonneg.mpr (by exact_mod_cast (le_of_lt hm_lt_q))
    have htwo_nonneg : (0 : ℚ) ≤ 2 := by norm_num
    exact div_nonneg hsub_nonneg htwo_nonneg
  have h_natInt_expr :
      (Nat.ceil (((q : ℚ) - m) / 2) : ℝ) =
        (Int.ceil (((q : ℝ) - (m : ℝ)) / 2) : ℝ) := by
    have h1 : (Nat.ceil xQ : ℝ) = (Int.ceil xQ : ℝ) := by
      exact_mod_cast
        (Int.natCast_ceil_eq_ceil (R := ℚ) (a := xQ) hxQ_nonneg)
    have h2 : (Int.ceil xQ : ℝ) = (Int.ceil (xQ : ℝ) : ℝ) := by
      exact_mod_cast (Rat.ceil_cast (α := ℝ) xQ).symm
    have hx : (xQ : ℝ) = xR := by
      simp [xQ, xR]
    calc
      (Nat.ceil (((q : ℚ) - m) / 2) : ℝ)
          = (Nat.ceil xQ : ℝ) := rfl
      _ = (Int.ceil xQ : ℝ) := h1
      _ = (Int.ceil (xQ : ℝ) : ℝ) := h2
      _ = (Int.ceil xR : ℝ) := by simp [hx]
  have hA_nat_real :
      (2 * J * Nat.ceil (((q : ℚ) - m) / 2) : ℝ) =
        (2 * (J : ℝ)) * (Int.ceil xR : ℝ) := by
    simp [h_natInt_expr, xR]
  have hB_lt_A_nat_real :
      (B : ℝ) <
        (2 * J * Nat.ceil (((q : ℚ) - m) / 2) : ℝ) := by
    simpa [hA_nat_real, D, hD_def] using hB_lt_A_real
  exact
    (by
      exact_mod_cast hB_lt_A_nat_real :
        2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B)

lemma exists_nonzero_solution_of_finrank_lt
    (F : Type*) [Field F]
    (V W : Type*) [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (L : V →ₗ[F] W)
    (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ L v = 0 :=
by
  classical
  obtain ⟨v, hv_mem, hv_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (p := LinearMap.ker L)
      (LinearMap.ker_ne_bot_of_finrank_lt (f := L) h)
  refine ⟨v, hv_ne, ?_⟩
  simpa using hv_mem

lemma natDegree_le_of_mem_degreeLT_succ
    (F : Type*) [Semiring F] (d : ℕ) (p : Polynomial.degreeLT F (d + 1)) :
    (p : Polynomial F).natDegree ≤ d :=
by
  have h := p.2
  simp only [Polynomial.mem_degreeLT] at h
  refine Nat.lt_succ_iff.mp ?_
  by_cases hp : (p : Polynomial F) = 0
  · simp [hp]
  · rw [Polynomial.degree_eq_natDegree hp] at h
    exact WithBot.coe_lt_coe.mp h

lemma stepanov_dimension_inequality_ceil
    (F : Type*) [Field F]
    (ℓ d m q B : ℕ)
    (hℓ_pos : 0 < ℓ) (hm_ge_two : 2 ≤ m)
    (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
    (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ,
      (Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) + d + k * (m - 1))) :
  let J := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
  Module.finrank F (Fin B → F) <
    Module.finrank F (Fin (2 * J) → Polynomial.degreeLT F (d + 1)) :=
by
  intro J
  have hceil_nat : 1 ≤ Nat.ceil (((q : ℚ) - m) / 2) := by
    refine Nat.one_le_ceil_iff.mpr ?_
    have hm_lt_q : m < q :=
      lt_of_le_of_lt (Nat.le_mul_of_pos_left m (by decide : 0 < 6)) (by simpa using hq6m)
    have : (0 : ℚ) < (q : ℚ) - m :=
      sub_pos.mpr (by exact_mod_cast hm_lt_q)
    simpa using div_pos this (show (0 : ℚ) < (2 : ℚ) by norm_num)
  have hA_gt_B :
      2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B :=
    stepanov_system_dimension_inequality_nat q m ℓ hm_ge_two hq6m hl hℓ_pos B
      (by simpa [hd] using hB)
  simpa [ Module.finrank_pi_fintype,
          Module.finrank_fintype_fun_eq_card,
          LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv F (d + 1)),
          hd, Nat.sub_add_cancel hceil_nat ] using hA_gt_B

noncomputable def polyMulRightLinear (F : Type*) [Field F] (g : Polynomial F) :
    Polynomial F →ₗ[F] Polynomial F :=
  LinearMap.mulRight F g

noncomputable def polyDivRightLinear (F : Type*) [Field F] {g : Polynomial F} (hg : g ≠ 0) :
    (LinearMap.range (polyMulRightLinear (F:=F) g)) →ₗ[F] Polynomial F :=
  (LinearEquiv.ofInjective (polyMulRightLinear (F:=F) g)
      (fun _ _ => mul_right_cancel₀ hg)).symm.toLinearMap

noncomputable def stepanovHasseQuotMap
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) :
    Polynomial F →ₗ[F] Polynomial F := by
  let g : Polynomial F := f ^ (r - k)
  let mulG : Polynomial F →ₗ[F] Polynomial F := polyMulRightLinear (F := F) g
  let numMap : Polynomial F →ₗ[F] Polynomial F :=
    (Polynomial.hasseDeriv k).comp (polyMulRightLinear (F := F) (f ^ r))
  have hmem : ∀ p, numMap p ∈ LinearMap.range mulG := by
    intro p
    have hdiv :
        f ^ (r - k) ∣ hasseDerivOp F k (p * f ^ r) :=
      hasseDerivOp_mul_pow_dvd F k r p f
    obtain ⟨q, hq⟩ := hdiv
    refine ⟨q, ?_⟩
    have hq' : hasseDerivOp F k (p * f ^ r) = q * f ^ (r - k) := by
      simpa [mul_comm] using hq
    simpa [numMap, mulG, g, hasseDerivOp] using hq'.symm
  exact
    (polyDivRightLinear (F := F) (g := g) (pow_ne_zero _ hf)).comp
      (LinearMap.codRestrict (LinearMap.range mulG) numMap hmem)

lemma stepanovHasseQuotMap_mul
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p * f ^ (r - k) =
      hasseDerivOp F k (p * f ^ r) :=
by
  set g : Polynomial F := f ^ (r - k) with hgdef
  set numMap : Polynomial F →ₗ[F] Polynomial F :=
    (Polynomial.hasseDeriv k).comp (polyMulRightLinear (F := F) (f ^ r)) with hnumMap
  have hmem : ∀ p, numMap p ∈ LinearMap.range (polyMulRightLinear (F := F) g) := by
    intro p
    rcases hasseDerivOp_mul_pow_dvd F k r p f with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simpa [numMap, g, hasseDerivOp, polyMulRightLinear, mul_comm] using hq.symm
  set z : LinearMap.range (polyMulRightLinear (F := F) g) :=
    LinearMap.codRestrict (LinearMap.range (polyMulRightLinear (F := F) g)) numMap hmem p
      with hz
  calc
    stepanovHasseQuotMap (F := F) (f := f) hf r k p * f ^ (r - k)
        = polyMulRightLinear (F := F) g
            (polyDivRightLinear (F := F) (g := g) (pow_ne_zero _ hf) z) := by
          simp [stepanovHasseQuotMap, hz, g, numMap,
            polyMulRightLinear, LinearMap.comp_apply]
    _ = z := by
          simp [polyDivRightLinear]
    _ = numMap p := rfl
    _ = hasseDerivOp F k (p * f ^ r) := by
      simp [numMap, polyMulRightLinear, LinearMap.comp_apply, hasseDerivOp]

lemma stepanovHasseQuotMap_eq_div
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p =
      hasseDerivOp F k (p * f ^ r) / f ^ (r - k) :=
by
  refine mul_right_cancel₀ (pow_ne_zero (r - k) hf) ?_
  refine (stepanovHasseQuotMap_mul (F := F) (f := f) hf r k p).trans ?_
  simpa [mul_comm] using
    (EuclideanDomain.mul_div_cancel'
      (a := hasseDerivOp F k (p * f ^ r))
      (b := f ^ (r - k))
      (pow_ne_zero (r - k) hf)
      (hasseDerivOp_mul_pow_dvd F k r p f)).symm

lemma stepanovHasseQuotMap_eq_div_left
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p =
      hasseDerivOp F k (f ^ r * p) / f ^ (r - k) :=
by simpa [mul_comm] using stepanovHasseQuotMap_eq_div (F := F) hf r k p

lemma stepanovHasseQuotMap_natDegree_le
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (m d r k : ℕ) (hfdeg : f.natDegree = m) (hk : k ≤ r)
    (p : Polynomial F) (hp : p.natDegree ≤ d) :
    (stepanovHasseQuotMap (F := F) (f := f) hf r k p).natDegree
      ≤ d + k * (m - 1) :=
by
  obtain ⟨rjk, _, hr_eq, -, hdeg_rjk, -⟩ :=
    auxiliary_derivatives (F := F) f m d r 0 hfdeg p 0 hp (by simp) k hk
  have h_eq :
      stepanovHasseQuotMap (F := F) (f := f) hf r k p = rjk := by
    refine mul_right_cancel₀ (pow_ne_zero (r - k) hf) ?_
    have hmul :=
      stepanovHasseQuotMap_mul (F := F) (f := f) hf r k p
    have hr_eq' : hasseDerivOp F k (p * f ^ r) = rjk * f ^ (r - k) := by
      simpa [mul_comm] using hr_eq
    simpa [hmul] using hr_eq'
  simpa [h_eq] using hdeg_rjk

lemma finrank_stepanov_constraint_space
    (F : Type*) [Field F] (ℓ J d m : ℕ) :
    Module.finrank F (∀ k : Fin ℓ, Polynomial.degreeLT F (J + d + k * (m - 1))) =
      ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) :=
by
  calc
    Module.finrank F (∀ k : Fin ℓ, Polynomial.degreeLT F (J + d + k * (m - 1)))
        = ∑ k : Fin ℓ, (J + d + k * (m - 1)) := by
          simp [Module.finrank_pi_fintype,
            Module.finrank_fintype_fun_eq_card,
            LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv F _)]
    _ = ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) := by
          simpa using
            (Fin.sum_univ_eq_sum_range (n := ℓ) (fun k => J + d + k * (m - 1)))

lemma stepanov_system_has_solution
  (F : Type*) [Field F] [Fintype F]
  (f : Polynomial F) (q m ℓ : ℕ) (a : F)
  (_hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
  (hm_ge_two : 2 ≤ m) (_hm_pos : 0 < m) (hℓ_pos : 0 < ℓ)
  (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
  (hJ_pos :
      1 ≤ Nat.ceil (((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)))) :
  let d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1
  let J : ℕ := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
  ∃ rj sj : ℕ → Polynomial F,
    (∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0) ∧
    (∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d) ∧
    (∀ x : F, f.eval x ≠ 0 → (f.eval x) ^ ((q - 1) / 2) = a →
      ∀ k < ℓ,
        Finset.sum (Finset.range J)
          (fun j =>
            (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
              a *
                ((hasseDerivOp F k (f ^ (ℓ + ((q - 1) / 2)) * sj j)) /
                    f ^ (ℓ + ((q - 1) / 2) - k)).eval x) *
              x ^ j) = 0) :=
by
  set d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1 with hd
  set J : ℕ := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) with hJdef
  simp [d, J]
  have hf : f ≠ 0 := by
    rintro hf0
    have hm0 : m = 0 := by simpa [hf0] using hfdeg.symm
    have : (2 : ℕ) ≤ 0 := by simp [hm0] at hm_ge_two
    exact (by decide : ¬ (2 ≤ 0)) this
  let c : ℕ := (q - 1) / 2
  let V := Fin (2 * J) → Polynomial.degreeLT F (d + 1)
  let W := ∀ k : Fin ℓ, Polynomial.degreeLT F (J + d + k * (m - 1))
  let finLeft : Fin J → Fin (2 * J) := fun j =>
    ⟨j, lt_of_lt_of_le j.isLt (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))⟩
  let finRight : Fin J → Fin (2 * J) := fun j =>
    ⟨J + j, by simp [two_mul, add_comm]⟩
  let piProj : Fin (2 * J) → V →ₗ[F] Polynomial.degreeLT F (d + 1) :=
    fun i => LinearMap.proj i
  let rjMap : Fin J → V →ₗ[F] Polynomial F := fun j =>
    (Polynomial.degreeLT F (d + 1)).subtype.comp (piProj (finLeft j))
  let sjMap : Fin J → V →ₗ[F] Polynomial F := fun j =>
    (Polynomial.degreeLT F (d + 1)).subtype.comp (piProj (finRight j))
  let rjkMap : Fin ℓ → Fin J → V →ₗ[F] Polynomial F := fun k j =>
    (stepanovHasseQuotMap (F := F) (f := f) hf ℓ k.1).comp (rjMap j)
  let sjkMap : Fin ℓ → Fin J → V →ₗ[F] Polynomial F := fun k j =>
    (stepanovHasseQuotMap (F := F) (f := f) hf (ℓ + c) k.1).comp (sjMap j)
  let sigmaMap : Fin ℓ → V →ₗ[F] Polynomial F := fun k =>
    Finset.sum (Finset.univ : Finset (Fin J))
      (fun j =>
        (polyMulRightLinear (F := F) (Polynomial.X ^ (j : ℕ))).comp
          (rjkMap k j + a • sjkMap k j))
  have h_sigma_deg :
      ∀ k : Fin ℓ, ∀ v : V,
        (sigmaMap k v).natDegree ≤ J - 1 + d + k * (m - 1) := by
    intro k v
    let rjkFin : Fin J → Polynomial F := fun j => rjkMap k j v
    let sjkFin : Fin J → Polynomial F := fun j => sjkMap k j v
    have hdeg_r : ∀ j : Fin J, (rjkFin j).natDegree ≤ d + k * (m - 1) := by
      intro j
      have hk_le : k.1 ≤ ℓ := Nat.le_of_lt k.isLt
      simp only [rjkFin, rjkMap, rjMap]
      exact
        stepanovHasseQuotMap_natDegree_le (F := F) hf m d ℓ k.1 hfdeg hk_le
          _ (natDegree_le_of_mem_degreeLT_succ F d (piProj (finLeft j) v))
    have hdeg_s : ∀ j : Fin J, (sjkFin j).natDegree ≤ d + k * (m - 1) := by
      intro j
      have hk_le : k.1 ≤ ℓ + c := le_trans (Nat.le_of_lt k.isLt) (Nat.le_add_right _ _)
      simp only [sjkFin, sjkMap, sjMap]
      exact
        stepanovHasseQuotMap_natDegree_le (F := F) hf m d (ℓ + c) k.1 hfdeg hk_le
          _ (natDegree_le_of_mem_degreeLT_succ F d (piProj (finRight j) v))
    have hdeg_sum :=
      stepanov_sigma_degree_bound_fin (F := F) (d := d) (k := k) (m := m) (J := J)
        (a := a) rjkFin sjkFin hdeg_r hdeg_s
    have hsum :
        sigmaMap k v =
          ∑ j : Fin J, (rjkFin j + Polynomial.C a * sjkFin j) * Polynomial.X ^ (j : ℕ) := by
      simp [sigmaMap, rjkFin, sjkFin, polyMulRightLinear,
        LinearMap.add_apply, LinearMap.smul_apply, Polynomial.smul_eq_C_mul]
    simpa [hsum] using hdeg_sum
  let sigmaMapLT :
      (k : Fin ℓ) → V →ₗ[F] Polynomial.degreeLT F (J + d + k * (m - 1)) :=
    fun k =>
      LinearMap.codRestrict (Polynomial.degreeLT F (J + d + k * (m - 1))) (sigmaMap k) (by
        intro v
        by_cases hzero : sigmaMap k v = 0
        · simp [hzero]
        · have hdeg_nat : (sigmaMap k v).natDegree < J + d + k * (m - 1) := by
            have hlt : J - 1 + d + k * (m - 1) < J + d + k * (m - 1) := by
              omega
            exact lt_of_le_of_lt (h_sigma_deg k v) hlt
          have hdeg : (sigmaMap k v).degree < (J + d + k * (m - 1) : ℕ) :=
            (Polynomial.natDegree_lt_iff_degree_lt hzero).1 hdeg_nat
          simpa [Polynomial.mem_degreeLT] using hdeg)
  let L : V →ₗ[F] W := LinearMap.pi (fun k => sigmaMapLT k)
  set B : ℕ := ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) with hBdef
  have hW_finrank : Module.finrank F W = B := by
    simpa [W, hBdef] using finrank_stepanov_constraint_space F ℓ J d m
  have h_dim :
      Module.finrank F (Fin B → F) <
        Module.finrank F V := by
    have hB_le : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) := by
      simp [B]
    have h := stepanov_dimension_inequality_ceil
      (F := F) (ℓ := ℓ) (d := d) (m := m) (q := q) (B := B)
      hℓ_pos hm_ge_two hq6m hl hd
      (by
        simpa [J, hJdef, add_comm, add_left_comm, add_assoc] using hB_le)
    simpa [J, hJdef, V] using h
  have hB_lt : B < Module.finrank F V := by
    have hFin : Module.finrank F (Fin B → F) = B := by simp
    simpa [hFin] using h_dim
  have hW_lt : Module.finrank F W < Module.finrank F V := by
    simpa [hW_finrank] using hB_lt
  obtain ⟨v, hv_ne, hv_zero⟩ :=
    exists_nonzero_solution_of_finrank_lt (L := L) (h := by simpa [V] using hW_lt)
  let rj : ℕ → Polynomial F := fun j =>
    if hj : j < J then (rjMap ⟨j, hj⟩ v) else 0
  let sj : ℕ → Polynomial F := fun j =>
    if hj : j < J then (sjMap ⟨j, hj⟩ v) else 0
  have h_nonzero : ∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0 := by
    by_contra h
    push_neg at h
    have hv_zero' : v = 0 := by
      funext i
      have hi : (i : ℕ) < J ∨ J ≤ (i : ℕ) := lt_or_ge (i : ℕ) J
      cases hi with
      | inl hlt =>
          have : rj i = 0 := (h i hlt).1
          simpa [rj, hlt, rjMap, piProj, finLeft] using this
      | inr hge =>
          have hj : (i : ℕ) - J < J := by
            have hlt : (i : ℕ) < 2 * J := i.isLt
            omega
          have : sj ((i : ℕ) - J) = 0 := (h ((i : ℕ) - J) hj).2
          have hidx : finRight ⟨(i : ℕ) - J, hj⟩ = i := by
            ext
            simp [finRight, Nat.add_sub_of_le hge]
          simpa [sj, hj, sjMap, piProj, hidx] using this
    exact hv_ne hv_zero'
  have hdeg :
      ∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d := by
    intro j hj
    have hr : (rj j).natDegree ≤ d := by
      simp [rj, hj, rjMap, piProj, finLeft,
        natDegree_le_of_mem_degreeLT_succ]
    have hs : (sj j).natDegree ≤ d := by
      simp [sj, hj, sjMap, piProj, finRight,
        natDegree_le_of_mem_degreeLT_succ]
    exact ⟨hr, hs⟩
  have hvan :
      ∀ x : F, f.eval x ≠ 0 → (f.eval x) ^ c = a →
        ∀ k < ℓ,
          Finset.sum (Finset.range J)
            (fun j =>
              (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
                  a *
                    ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) /
                        f ^ (ℓ + c - k)).eval x) *
                x ^ j) = 0 := by
    intro x _hx _hxa k hk
    have hLk : sigmaMapLT ⟨k, hk⟩ v = 0 := by
      simpa using congrArg (fun f => f ⟨k, hk⟩) hv_zero
    have hpoly_zero : sigmaMap ⟨k, hk⟩ v = 0 := by
      have := congrArg Subtype.val hLk
      simpa [sigmaMapLT] using this
    have hsum_eval :
        (sigmaMap ⟨k, hk⟩ v).eval x =
          Finset.sum (Finset.range J)
            (fun j =>
              (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
                  a *
                    ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) /
                        f ^ (ℓ + c - k)).eval x) *
                x ^ j) := by
      classical
      let p : Fin J → Polynomial F := fun j =>
        hasseDerivOp F k (f ^ ℓ * (rjMap j v)) / f ^ (ℓ - k) +
          Polynomial.C a *
            (hasseDerivOp F k (f ^ (ℓ + c) * (sjMap j v)) / f ^ (ℓ + c - k))
      have hsum_poly :
          sigmaMap ⟨k, hk⟩ v =
            ∑ j : Fin J,
              p j * Polynomial.X ^ (j : ℕ) := by
        simp [p, sigmaMap, rjkMap, sjkMap, stepanovHasseQuotMap_eq_div_left,
          polyMulRightLinear, LinearMap.comp_apply, LinearMap.add_apply,
          LinearMap.smul_apply, Polynomial.smul_eq_C_mul]
      have hsum_eval_fin :
          (sigmaMap ⟨k, hk⟩ v).eval x =
            ∑ j : Fin J,
              (p j).eval x * x ^ (j : ℕ) := by
        have :=
          (Polynomial.eval_finset_sum (s := (Finset.univ : Finset (Fin J)))
            (g := fun j : Fin J => p j * Polynomial.X ^ (j : ℕ)) (x := x))
        simpa [hsum_poly] using this
      have hsum_eval_fin' :
          (sigmaMap ⟨k, hk⟩ v).eval x =
            ∑ j : Fin J,
              ((hasseDerivOp F k (f ^ ℓ * (rjMap j v)) / f ^ (ℓ - k)).eval x +
                a *
                  (hasseDerivOp F k (f ^ (ℓ + c) * (sjMap j v)) /
                    f ^ (ℓ + c - k)).eval x) *
                x ^ (j : ℕ) := by
        simpa [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          mul_add, mul_assoc] using hsum_eval_fin
      let G : Fin J → F := fun j =>
        ((hasseDerivOp F k (f ^ ℓ * (rjMap j v)) / f ^ (ℓ - k)).eval x +
            a *
              (hasseDerivOp F k (f ^ (ℓ + c) * (sjMap j v)) /
                f ^ (ℓ + c - k)).eval x) *
          x ^ (j : ℕ)
      have hsum_eval_finG :
          (sigmaMap ⟨k, hk⟩ v).eval x = ∑ j : Fin J, G j := by
        simpa [G] using hsum_eval_fin'
      let GNat : ℕ → F := fun j =>
        if hj : j < J then G ⟨j, hj⟩ else 0
      have hsum_eval_finGNat :
          (sigmaMap ⟨k, hk⟩ v).eval x = ∑ j : Fin J, GNat j := by
        refine hsum_eval_finG.trans ?_
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [GNat, j.isLt]
      have hsum_range := (Fin.sum_univ_eq_sum_range (n := J) (f := GNat))
      refine (hsum_eval_finGNat.trans hsum_range).trans ?_
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj' : j < J := by
        simpa using (Finset.mem_range.mp hj)
      simp [GNat, G, rj, sj, hj']
    have : (sigmaMap ⟨k, hk⟩ v).eval x = 0 := by
      simp [hpoly_zero]
    simpa [hsum_eval] using this
  refine ⟨rj, sj, h_nonzero, hdeg, hvan⟩

lemma stepanov_constructed_nonzero
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q m ℓ J c d : ℕ)
  (hq : q = Fintype.card F) (hfdeg : f.natDegree = m) (hc : c = (q - 1) / 2)
  (hm_pos : 0 < m)
  (hq6m : q > 6 * m)
  (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (rj sj : ℕ → Polynomial F)
  (hdeg : ∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d)
  (hnz : ∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0) :
  f^ℓ * (Finset.sum (Finset.range J)
    (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))) ≠ 0 :=
by
  intro hz
  have hzero :=
    (stepanov_nonzero F hF f q m ℓ J c hc hq hfdeg hm_pos hq6m rj sj hnsq
      (by simpa [hd] using hdeg)).1 hz
  rcases hnz with ⟨j, hj, h_or⟩
  exact h_or.elim (· (hzero j hj).1) (· (hzero j hj).2)
