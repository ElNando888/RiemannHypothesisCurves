import Mathlib
import RiemannHypothesisCurves.HasseDerivatives

lemma auxiliary_derivatives (F : Type*) [Field F]
    (f : Polynomial F) (m d ℓ c : ℕ)
    (hfdeg : f.natDegree = m)
    (rj sj : Polynomial F) (hr : rj.natDegree ≤ d) (hs : sj.natDegree ≤ d)
    (k : ℕ) (hk : k ≤ ℓ) :
  ∃ rjk sjk : Polynomial F,
    hasseDerivOp F k (f^ℓ * rj) = rjk * f^(ℓ - k) ∧
    hasseDerivOp F k (f^(ℓ + c) * sj) = sjk * f^(ℓ + c - k) ∧
    rjk.natDegree ≤ d + k * (m - 1) ∧ sjk.natDegree ≤ d + k * (m - 1) :=
by
  by_cases hf0 : f = 0
  · subst hf0
    have hm0 : m = 0 := by
      simpa [Polynomial.natDegree_zero] using hfdeg.symm
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨rj, sj, ?_, ?_, ?_, ?_⟩
      · simp [hasseDerivOp, mul_comm]
      · simp [hasseDerivOp, mul_comm]
      · simpa [hm0]
      · simpa [hm0]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hℓpos : 0 < ℓ := lt_of_lt_of_le hkpos hk
      refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
      · have hpow : (0 : Polynomial F) ^ ℓ = 0 := by
          have hne : ℓ ≠ 0 := ne_of_gt hℓpos
          simp [hne]
        simp [hasseDerivOp, hpow]
      · have hℓcpos : 0 < ℓ + c := lt_of_lt_of_le hℓpos (Nat.le_add_right _ _)
        have hpow : (0 : Polynomial F) ^ (ℓ + c) = 0 := by
          have hne : ℓ + c ≠ 0 := ne_of_gt hℓcpos
          simpa [hne] using (zero_pow (M₀ := Polynomial F) (n := ℓ + c) hne)
        simp [hasseDerivOp, hpow]
      · simp [hm0]
      · simp [hm0]
  · have hdeg_f_eq : Polynomial.degree f = (m : WithBot ℕ) := by
      simpa [hfdeg] using Polynomial.degree_eq_natDegree hf0
    obtain ⟨_, hℓ⟩ := hasse_formulas F k ℓ hk
    rcases hℓ rj f with ⟨hdiv_rj_core, hdeg_rj_core⟩
    have hdiv_rj : f ^ (ℓ - k) ∣ hasseDerivOp F k (f ^ ℓ * rj) := by
      simpa [mul_comm] using hdiv_rj_core
    have hkℓc : k ≤ ℓ + c := le_trans hk (Nat.le_add_right _ _)
    obtain ⟨_, hℓc⟩ := hasse_formulas F k (ℓ + c) hkℓc
    rcases hℓc sj f with ⟨hdiv_sj_core, hdeg_sj_core⟩
    have hdiv_sj : f ^ (ℓ + c - k) ∣ hasseDerivOp F k (f ^ (ℓ + c) * sj) := by
      simpa [mul_comm] using hdiv_sj_core
    set rjk : Polynomial F :=
      hasseDerivOp F k (f ^ ℓ * rj) / f ^ (ℓ - k) with hrjk_def
    set sjk : Polynomial F :=
      hasseDerivOp F k (f ^ (ℓ + c) * sj) / f ^ (ℓ + c - k) with hsjk_def
    have hr_eq : hasseDerivOp F k (f ^ ℓ * rj) = rjk * f ^ (ℓ - k) := by
      simpa [hrjk_def, mul_comm] using
        (EuclideanDomain.mul_div_cancel'
          (R := Polynomial F)
          (a := hasseDerivOp F k (f ^ ℓ * rj))
          (b := f ^ (ℓ - k)) (pow_ne_zero _ hf0) hdiv_rj).symm
    have hs_eq : hasseDerivOp F k (f ^ (ℓ + c) * sj) = sjk * f ^ (ℓ + c - k) := by
      simpa [hsjk_def, mul_comm] using
        (EuclideanDomain.mul_div_cancel'
          (R := Polynomial F)
          (a := hasseDerivOp F k (f ^ (ℓ + c) * sj))
          (b := f ^ (ℓ + c - k)) (pow_ne_zero _ hf0) hdiv_sj).symm
    have hdeg_rjk_match :
        Polynomial.degree rjk ≤
          (match
              Polynomial.degree rj + (k : WithBot ℕ) * Polynomial.degree f with
            | ⊥ => ⊥
            | some n => some (n - k)) := by
      simpa [hrjk_def, mul_comm] using hdeg_rj_core
    have hdeg_sjk_match :
        Polynomial.degree sjk ≤
          (match
              Polynomial.degree sj + (k : WithBot ℕ) * Polynomial.degree f with
            | ⊥ => ⊥
            | some n => some (n - k)) := by
      simpa [hsjk_def, mul_comm] using hdeg_sj_core
    have hdeg_rj_le_d : Polynomial.degree rj ≤ (d : WithBot ℕ) :=
      (Polynomial.natDegree_le_iff_degree_le).1 hr
    have hdeg_sj_le_d : Polynomial.degree sj ≤ (d : WithBot ℕ) :=
      (Polynomial.natDegree_le_iff_degree_le).1 hs
    let Ftrunc : WithBot ℕ → WithBot ℕ :=
      fun x => match x with | ⊥ => ⊥ | some n => some (n - k)
    have hF_mono :
        ∀ {x y : WithBot ℕ}, x ≤ y → Ftrunc x ≤ Ftrunc y := by
      intro x y hxy
      cases x using WithBot.recBotCoe with
      | bot =>
          cases y using WithBot.recBotCoe with
          | bot => simp [Ftrunc]
          | coe _ => simp [Ftrunc]
      | coe a =>
          cases y using WithBot.recBotCoe with
          | bot =>
              have hxbot : ((a : ℕ) : WithBot ℕ) = (⊥ : WithBot ℕ) :=
                (le_bot_iff).1 hxy
              exact (WithBot.natCast_ne_bot (α := ℕ) a) hxbot |> False.elim
          | coe b =>
              have hab : a ≤ b := (WithBot.coe_le_coe).1 hxy
              have hsub : a - k ≤ b - k := Nat.sub_le_sub_right hab k
              exact (WithBot.coe_le_coe).2 hsub
    let x_rj : WithBot ℕ :=
      Polynomial.degree rj + (k : WithBot ℕ) * Polynomial.degree f
    let x_sj : WithBot ℕ :=
      Polynomial.degree sj + (k : WithBot ℕ) * Polynomial.degree f
    let y : WithBot ℕ :=
      (d : WithBot ℕ) + (k : WithBot ℕ) * Polynomial.degree f
    have hx_rj_le_y : x_rj ≤ y := by
      have :=
        add_le_add_right hdeg_rj_le_d ((k : WithBot ℕ) * Polynomial.degree f)
      simpa [x_rj, y] using this
    have hx_sj_le_y : x_sj ≤ y := by
      have :=
        add_le_add_right hdeg_sj_le_d ((k : WithBot ℕ) * Polynomial.degree f)
      simpa [x_sj, y] using this
    have hF_xrj_le_y : Ftrunc x_rj ≤ Ftrunc y := hF_mono hx_rj_le_y
    have hF_xsj_le_y : Ftrunc x_sj ≤ Ftrunc y := hF_mono hx_sj_le_y
    have hF_y_eq :
        Ftrunc y = ((d + k * m - k : ℕ) : WithBot ℕ) := by
      have hy : y = ((d + k * m : ℕ) : WithBot ℕ) := by
        simp [y, hdeg_f_eq, mul_comm]
      have hyF : Ftrunc y = Ftrunc ((d + k * m : ℕ) : WithBot ℕ) :=
        congrArg Ftrunc hy
      simpa [Ftrunc] using hyF
    have hdeg_rjk_le :
        Polynomial.degree rjk ≤ ((d + k * m - k : ℕ) : WithBot ℕ) := by
      simpa [hF_y_eq] using
        (le_trans (by simpa [x_rj, Ftrunc] using hdeg_rjk_match) hF_xrj_le_y)
    have hdeg_sjk_le :
        Polynomial.degree sjk ≤ ((d + k * m - k : ℕ) : WithBot ℕ) := by
      simpa [hF_y_eq] using
        (le_trans (by simpa [x_sj, Ftrunc] using hdeg_sjk_match) hF_xsj_le_y)
    have hnat_rjk_le : rjk.natDegree ≤ d + k * m - k :=
      (Polynomial.natDegree_le_iff_degree_le).2 hdeg_rjk_le
    have hnat_sjk_le : sjk.natDegree ≤ d + k * m - k :=
      (Polynomial.natDegree_le_iff_degree_le).2 hdeg_sjk_le
    have h_nat_ineq : d + k * m - k ≤ d + k * (m - 1) := by
      cases m with
      | zero => simp
      | succ m' =>
          have : d + k * Nat.succ m' - k = d + k * m' := by
            simpa [Nat.mul_succ, Nat.add_assoc] using
              (Nat.add_sub_cancel (d + k * m') k)
          simp [this]
    refine ⟨rjk, sjk, hr_eq, hs_eq, ?_, ?_⟩
    · exact le_trans hnat_rjk_le h_nat_ineq
    · exact le_trans hnat_sjk_le h_nat_ineq

lemma hasseDerivOp_mul_Xqpow
  (F : Type*) [Field F] [Fintype F]
  (q k : ℕ) (hq : q = Fintype.card F) (hkq : k < q)
  (P : Polynomial F) (j : ℕ) :
  hasseDerivOp F k (P * (Polynomial.X : Polynomial F)^(j * q)) =
    hasseDerivOp F k P * (Polynomial.X : Polynomial F)^(j * q) :=
by
  have choose_mul_card_pow_cast_eq_zero
      (q j i : ℕ) (hq : q = Fintype.card F)
      (hi_pos : 0 < i) (hi_lt : i < q) :
      (Nat.choose (j * q) i : F) = 0 := by
    have hfrob :
        (1 + (Polynomial.X : Polynomial F)) ^ q =
          (1 : Polynomial F) ^ q +
            (Polynomial.X : Polynomial F) ^ q := by
      simpa [hq, FiniteField.coe_frobeniusAlgHom] using
        (FiniteField.frobeniusAlgHom F (Polynomial F)).map_add
          (1 : Polynomial F) (Polynomial.X : Polynomial F)
    have hpow :
        (1 + (Polynomial.X : Polynomial F)) ^ (j * q) =
          (1 + (Polynomial.X : Polynomial F) ^ q) ^ j := by
      have h1 :
          (1 + (Polynomial.X : Polynomial F)) ^ (j * q) =
            ((1 + (Polynomial.X : Polynomial F)) ^ q) ^ j := by
        simp [pow_mul, mul_comm]
      have h2 :
          ((1 + (Polynomial.X : Polynomial F)) ^ q) ^ j =
            (1 + (Polynomial.X : Polynomial F) ^ q) ^ j := by
        simpa [one_pow] using
          congrArg (fun p : Polynomial F => p ^ j) hfrob
      exact h1.trans h2
    have hcoeff_right_zero :
        ((1 + (Polynomial.X : Polynomial F) ^ q) ^ j).coeff i = 0 := by
      have h' : ∀ n : ℕ,
          ((1 + (Polynomial.X : Polynomial F) ^ q) ^ n).coeff i = 0 := by
        refine Nat.rec ?base ?step
        · have hi_ne_zero : i ≠ 0 := ne_of_gt hi_pos
          simp [pow_zero, Polynomial.coeff_one, hi_ne_zero]
        · intro n hn
          have hmul :
              (((1 + (Polynomial.X : Polynomial F) ^ q) ^ n) *
                  (Polynomial.X : Polynomial F) ^ q).coeff i = 0 := by
            simpa [Nat.not_le.mpr hi_lt] using
              (Polynomial.coeff_mul_X_pow'
                (p := (1 + (Polynomial.X : Polynomial F) ^ q) ^ n)
                (n := q) (d := i))
          have :
              ((1 + (Polynomial.X : Polynomial F) ^ q) ^ (n.succ)).coeff i =
                ((1 + (Polynomial.X : Polynomial F) ^ q) ^ n).coeff i +
                  (((1 + (Polynomial.X : Polynomial F) ^ q) ^ n) *
                      (Polynomial.X : Polynomial F) ^ q).coeff i := by
            simp [pow_succ, mul_add, Polynomial.coeff_add]
          simp [this, hn, hmul]
      exact h' j
    have hcoeff_left_zero :
        ((1 + (Polynomial.X : Polynomial F)) ^ (j * q)).coeff i = 0 := by
      simpa [congrArg (fun p : Polynomial F => p.coeff i) hpow.symm]
        using hcoeff_right_zero
    simpa [Polynomial.coeff_one_add_X_pow (R := F) (n := j * q) (k := i)]
      using hcoeff_left_zero

  have hasseDerivOp_X_pow_mul_card_eq_zero
      (j k : ℕ) (hq : q = Fintype.card F)
      (hk_pos : 0 < k) (hk_lt : k < q) :
      hasseDerivOp F k ((Polynomial.X : Polynomial F) ^ (j * q)) = 0 := by
    have hchoose_zero :
        (Nat.choose (j * q) k : F) = 0 :=
      choose_mul_card_pow_cast_eq_zero q j k hq hk_pos hk_lt
    simp [hasseDerivOp, Polynomial.X_pow_eq_monomial, hchoose_zero]

  cases k with
  | zero =>
      simp [hasseDerivOp, mul_comm]
  | succ k' =>
      have hmul :
          hasseDerivOp F (Nat.succ k')
              (P * (Polynomial.X : Polynomial F) ^ (j * q)) =
            ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
              hasseDerivOp F p.1 P *
                hasseDerivOp F p.2
                  ((Polynomial.X : Polynomial F) ^ (j * q)) := by
        simpa [hasseDerivOp, mul_comm, mul_left_comm, mul_assoc] using
          (Polynomial.hasseDeriv_mul (R := F) (k := Nat.succ k')
            (f := P)
            (g := (Polynomial.X : Polynomial F) ^ (j * q)))
      have hsum :
          ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
              hasseDerivOp F p.1 P *
                hasseDerivOp F p.2
                  ((Polynomial.X : Polynomial F) ^ (j * q)) =
            hasseDerivOp F (Nat.succ k') P *
              (Polynomial.X : Polynomial F) ^ (j * q) := by
        have h' :
            ∑ p ∈ Finset.antidiagonal (Nat.succ k'),
                hasseDerivOp F p.1 P *
                  hasseDerivOp F p.2
                    ((Polynomial.X : Polynomial F) ^ (j * q)) =
              hasseDerivOp F (Nat.succ k') P *
                hasseDerivOp F 0
                  ((Polynomial.X : Polynomial F) ^ (j * q)) := by
          refine
            Finset.sum_eq_single_of_mem
              (a := (Nat.succ k', 0))
              ?ha
              ?hothers
          · exact Finset.mem_antidiagonal.mpr (by simp)
          · intro p hp_mem hp_ne
            rcases p with ⟨a, b⟩
            change (a, b) ∈ _ at hp_mem
            change (a, b) ≠ (Nat.succ k', 0) at hp_ne
            have hsum_ab : a + b = Nat.succ k' :=
              Finset.mem_antidiagonal.mp hp_mem
            have hb_ne_zero : b ≠ 0 := by
              intro hb0
              have : a = Nat.succ k' := by
                simpa [hb0] using hsum_ab
              apply hp_ne
              ext <;> simp [this, hb0]
            have hb_pos : 0 < b := Nat.pos_of_ne_zero hb_ne_zero
            have hb_le : b ≤ Nat.succ k' := by
              have : b ≤ a + b := Nat.le_add_left _ _
              simpa [hsum_ab] using this
            have hb_ltq : b < q := lt_of_le_of_lt hb_le hkq
            have hderiv_zero :
                hasseDerivOp F b
                    ((Polynomial.X : Polynomial F) ^ (j * q)) = 0 :=
              hasseDerivOp_X_pow_mul_card_eq_zero j b hq hb_pos hb_ltq
            simp [hderiv_zero]
        simpa [hasseDerivOp] using h'
      simpa using (hmul.trans hsum)

lemma stepanov_form (F : Type*) [Field F] [Fintype F]
    (f : Polynomial F) (ℓ q c J k : ℕ) (hk : k < ℓ)
    (hq : q = Fintype.card F) (hkq : k < q)
    (rj sj : ℕ → Polynomial F) :
  ∃ rjk sjk : ℕ → Polynomial F,
    (∀ j, hasseDerivOp F k (f^ℓ * (rj j)) = (rjk j) * f^(ℓ - k)) ∧
    (∀ j, hasseDerivOp F k (f^(ℓ + c) * (sj j)) = (sjk j) * f^(ℓ + c - k)) ∧
    hasseDerivOp F k
      (f^ℓ *
        (Finset.sum (Finset.range J)
          (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q)))) =
      f^(ℓ - k) *
        Finset.sum (Finset.range J)
          (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) :=
by
  have h_ex :
      ∀ j : ℕ, ∃ rjk_j sjk_j : Polynomial F,
        hasseDerivOp F k (f^ℓ * (rj j)) = rjk_j * f^(ℓ - k) ∧
        hasseDerivOp F k (f^(ℓ + c) * (sj j)) = sjk_j * f^(ℓ + c - k) := by
    intro j
    let d := Nat.max (rj j).natDegree (sj j).natDegree
    have hr : (rj j).natDegree ≤ d := Nat.le_max_left _ _
    have hs : (sj j).natDegree ≤ d := Nat.le_max_right _ _
    obtain ⟨rjk_j, sjk_j, hr_eq, hs_eq, -, -⟩ :=
      auxiliary_derivatives (F := F) f f.natDegree d ℓ c rfl (rj j) (sj j) hr hs k hk.le
    exact ⟨rjk_j, sjk_j, hr_eq, hs_eq⟩
  choose rjk sjk hrjk hsjk using h_ex
  refine ⟨rjk, sjk, hrjk, hsjk, ?_⟩
  have h_rewrite :
      f^ℓ *
        Finset.sum (Finset.range J)
          (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q)) =
      Finset.sum (Finset.range J)
        (fun j => (f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q)) := by
    have h :=
      (Finset.mul_sum
        (s := Finset.range J)
        (f := fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))
        (a := f^ℓ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h_deriv_sum :
      hasseDerivOp F k
        (f^ℓ *
          Finset.sum (Finset.range J)
            (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))) =
      Finset.sum (Finset.range J)
        (fun j =>
          hasseDerivOp F k
            ((f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q))) := by
    simp [hasseDerivOp, h_rewrite, _root_.map_sum]
  have h_term :
      ∀ j : ℕ,
        hasseDerivOp F k
          ((f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q)) =
        f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q) := by
    intro j
    have h_split :
        f^ℓ * ((rj j) + (sj j) * f^c) =
          f^ℓ * (rj j) + f^(ℓ + c) * (sj j) := by
      simp [mul_add, pow_add, mul_comm, mul_left_comm]
    have hP_factor :
        hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
          f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) := by
      have h_add' :
          hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
            hasseDerivOp F k (f^ℓ * (rj j)) +
              hasseDerivOp F k (f^(ℓ + c) * (sj j)) := by
        simp [hasseDerivOp, h_split]
      have h_basic :
          hasseDerivOp F k (f^ℓ * (rj j)) +
              hasseDerivOp F k (f^(ℓ + c) * (sj j)) =
            (rjk j) * f^(ℓ - k) + (sjk j) * f^(ℓ + c - k) := by
        simp [hrjk j, hsjk j]
      have h_tmp :
          hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
            (rjk j) * f^(ℓ - k) + (sjk j) * f^(ℓ + c - k) :=
        h_add'.trans h_basic
      have h_exp : ℓ + c - k = c + (ℓ - k) := by
        have hℓ : ℓ = (ℓ - k) + k := (Nat.sub_add_cancel hk.le).symm
        have h_step : ℓ + c - k = ((ℓ - k) + k) + c - k := by
          have := congrArg (fun n => n + c - k) hℓ
          simpa using this
        have h' : ((ℓ - k) + k) + c - k = (ℓ - k) + c := by
          have htemp : ((ℓ - k) + k) + c = ((ℓ - k) + c) + k := by
            calc
              ((ℓ - k) + k) + c
                  = (ℓ - k) + (k + c) := by
                        simp [Nat.add_assoc]
              _ = (ℓ - k) + (c + k) := by
                        simp [Nat.add_comm]
              _ = ((ℓ - k) + c) + k := by
                        simp [Nat.add_assoc]
          calc
            ((ℓ - k) + k) + c - k
                = ((ℓ - k) + c) + k - k := by
                      simp [htemp]
            _ = (ℓ - k) + c := by
                      simp
        have h1 : ℓ + c - k = (ℓ - k) + c := h_step.trans h'
        have h2 : (ℓ - k) + c = c + (ℓ - k) := Nat.add_comm _ _
        exact h1.trans h2
      have hpow : f^(ℓ + c - k) = f^c * f^(ℓ - k) := by
        have hpow' := congrArg (fun n => f^n) h_exp
        simpa [pow_add] using hpow'
      calc
        hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) =
            (rjk j) * f^(ℓ - k) + (sjk j) * f^(ℓ + c - k) := h_tmp
        _ = (rjk j) * f^(ℓ - k) + (sjk j) * (f^c * f^(ℓ - k)) := by
              exact congrArg
                (fun t => (rjk j) * f^(ℓ - k) + (sjk j) * t) hpow
        _ = rjk j * f^(ℓ - k) + sjk j * f^c * f^(ℓ - k) := by
              simp [mul_assoc]
        _ = (rjk j + sjk j * f^c) * f^(ℓ - k) := by
              simp [add_mul, mul_assoc]
        _ = f^(ℓ - k) * (rjk j + sjk j * f^c) := by
              ac_rfl
    have h_prod :=
      hasseDerivOp_mul_Xqpow (F := F) (q := q) (k := k)
        (hq := hq) (hkq := hkq)
        (P := f^ℓ * ((rj j) + (sj j) * f^c)) (j := j)
    calc
      hasseDerivOp F k
          ((f^ℓ * ((rj j) + (sj j) * f^c)) * (Polynomial.X)^(j*q)) =
          hasseDerivOp F k (f^ℓ * ((rj j) + (sj j) * f^c)) *
            (Polynomial.X)^(j*q) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h_prod
      _ = f^(ℓ - k) * (rjk j + sjk j * f^c) * (Polynomial.X)^(j*q) := by
            simp [hP_factor]
      _ = f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q) := by
            ac_rfl
  have h_deriv_explicit :
      hasseDerivOp F k
        (f^ℓ *
          Finset.sum (Finset.range J)
            (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q))) =
      Finset.sum (Finset.range J)
        (fun j =>
          f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by
    simpa [h_term] using h_deriv_sum
  have h_factor :
      Finset.sum (Finset.range J)
        (fun j =>
          f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) =
      f^(ℓ - k) *
        Finset.sum (Finset.range J)
          (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by
    have h1 :
        Finset.sum (Finset.range J)
          (fun j =>
            f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) =
        Finset.sum (Finset.range J)
          (fun j =>
            f^(ℓ - k) * (((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q))) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [mul_assoc]
    have h_mul_sum :=
      (Finset.mul_sum
        (s := Finset.range J)
        (f :=
          fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q))
        (a := f^(ℓ - k)))
    calc
      Finset.sum (Finset.range J)
          (fun j =>
            f^(ℓ - k) * ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) =
          Finset.sum (Finset.range J)
            (fun j =>
              f^(ℓ - k) * (((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q))) := h1
      _ = f^(ℓ - k) *
            Finset.sum (Finset.range J)
              (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by
            simpa using h_mul_sum.symm
  exact h_deriv_explicit.trans h_factor
