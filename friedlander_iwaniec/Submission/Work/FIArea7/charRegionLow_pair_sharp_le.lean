import Mathlib
import Submission.Work.FIArea7.Area7Regions6b
import Submission.Work.FIArea7.UniCharTerm6
import Submission.Work.FIArea7.Section16Expansion
import Submission.Work.FIArea7.WUniOmega6Pull6CharLow_aux
import Submission.Work.FIArea7.card_gBox_filter_mod
import Submission.Work.FIArea7.sum_inv_sq_Icc_le_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-! ## The honest class count (fibre bound + Cauchy–Schwarz over the classes) -/

/-- **The honest class count.**  The `ℓ²`-mass of the class aggregates of a coefficient `c` over the
residue-class partition of the box `gBox R` by the class map `unitClassD Q` (restricted to the
units, where it is a genuine class map) is at most `((2R+1).toNat / Q + 1)²` times the `ℓ²`-mass of
`c` on the box. -/
theorem classAggregate_le (Q : ℕ) [NeZero Q] (R : ℤ) (c : GaussianInt → ℂ) :
    ∑ a : GaussUnit Q,
        ‖∑ z ∈ (Work.FIPlan.gBox R).filter
            (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q ∧ unitClassD Q z = a),
          c z‖ ^ 2
      ≤ (((2 * R + 1).toNat / Q + 1) ^ 2 : ℕ) * ∑ z ∈ Work.FIPlan.gBox R, ‖c z‖ ^ 2 := by
  classical
  have hQ : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  set G : Finset GaussianInt :=
      (Work.FIPlan.gBox R).filter (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q) with hG
  -- the two forms of the class fibre agree
  have hfib : ∀ a : GaussUnit Q,
      (Work.FIPlan.gBox R).filter
          (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q ∧ unitClassD Q z = a)
        = G.filter (fun z => unitClassD Q z = a) := by
    intro a
    rw [hG, Finset.filter_filter]
  have keyZ : ∀ u : ZMod Q, u = ((u.val : ℤ) : ZMod Q) := fun u => by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_zmod_val u).symm
  -- the fibre count
  have hcard : ∀ a : GaussUnit Q, (((G.filter (fun z => unitClassD Q z = a)).card : ℝ))
      ≤ ((((2 * R + 1).toNat / Q + 1) ^ 2 : ℕ) : ℝ) := by
    intro a
    have hsub : G.filter (fun z => unitClassD Q z = a) ⊆
        (Work.FIPlan.gBox R).filter (fun z =>
          ((z.re : ZMod Q) = ((a.1.1.val : ℤ) : ZMod Q)) ∧
          ((z.im : ZMod Q) = ((a.1.2.val : ℤ) : ZMod Q))) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      obtain ⟨hzG, hza⟩ := hz
      rw [hG, Finset.mem_filter] at hzG
      obtain ⟨hzbox, hcop⟩ := hzG
      have hclass : Work.FIArea7.gaussUnitOf Q z hcop = a := by
        rw [← unitClassD_eq Q z hcop]; exact hza
      have hcoord : Work.FIArea7.gaussCoord Q z = a.1 := by
        have := congrArg Subtype.val hclass
        rwa [Work.FIArea7.gaussUnitOf_val] at this
      have h1 : (z.re : ZMod Q) = a.1.1 := by
        have := congrArg Prod.fst hcoord
        simpa [Work.FIArea7.gaussCoord] using this
      have h2 : (z.im : ZMod Q) = a.1.2 := by
        have := congrArg Prod.snd hcoord
        simpa [Work.FIArea7.gaussCoord] using this
      refine ⟨hzbox, ?_, ?_⟩
      · rw [h1]; exact keyZ a.1.1
      · rw [h2]; exact keyZ a.1.2
    have h1 : (G.filter (fun z => unitClassD Q z = a)).card
        ≤ (((2 * R + 1).toNat / Q + 1) ^ 2) := by
      rw [pow_two]
      exact le_trans (Finset.card_le_card hsub)
        (Work.FIArea7.card_gBox_filter_mod R Q hQ a.1.1.val a.1.2.val)
    exact_mod_cast h1
  -- per class Cauchy–Schwarz
  have hCS : ∀ a : GaussUnit Q,
      ‖∑ z ∈ G.filter (fun z => unitClassD Q z = a), c z‖ ^ 2
        ≤ ((((2 * R + 1).toNat / Q + 1) ^ 2 : ℕ) : ℝ)
            * ∑ z ∈ G.filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2 := by
    intro a
    set s := G.filter (fun z => unitClassD Q z = a) with hs
    have h1 : ‖∑ z ∈ s, c z‖ ≤ ∑ z ∈ s, ‖c z‖ := norm_sum_le _ _
    have h2 : (∑ z ∈ s, ‖c z‖) ^ 2 ≤ (s.card : ℝ) * ∑ z ∈ s, ‖c z‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    calc ‖∑ z ∈ s, c z‖ ^ 2 ≤ (∑ z ∈ s, ‖c z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (s.card : ℝ) * ∑ z ∈ s, ‖c z‖ ^ 2 := h2
      _ ≤ ((((2 * R + 1).toNat / Q + 1) ^ 2 : ℕ) : ℝ) * ∑ z ∈ s, ‖c z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hcard a) (Finset.sum_nonneg (fun z _ => sq_nonneg _))
  -- the fibres partition the units of the box
  have hpart : ∑ a : GaussUnit Q, ∑ z ∈ G.filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2
      = ∑ z ∈ G, ‖c z‖ ^ 2 :=
    Finset.sum_fiberwise G (fun z : GaussianInt => unitClassD Q z) (fun z => ‖c z‖ ^ 2)
  calc ∑ a : GaussUnit Q,
        ‖∑ z ∈ (Work.FIPlan.gBox R).filter
            (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q ∧ unitClassD Q z = a), c z‖ ^ 2
      = ∑ a : GaussUnit Q, ‖∑ z ∈ G.filter (fun z => unitClassD Q z = a), c z‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hfib a]
    _ ≤ ∑ a : GaussUnit Q, ((((2 * R + 1).toNat / Q + 1) ^ 2 : ℕ) : ℝ)
            * ∑ z ∈ G.filter (fun z => unitClassD Q z = a), ‖c z‖ ^ 2 :=
        Finset.sum_le_sum (fun a _ => hCS a)
    _ = ((((2 * R + 1).toNat / Q + 1) ^ 2 : ℕ) : ℝ) * ∑ z ∈ G, ‖c z‖ ^ 2 := by
        rw [← Finset.mul_sum, hpart]
    _ ≤ ((((2 * R + 1).toNat / Q + 1) ^ 2 : ℕ) : ℝ)
          * ∑ z ∈ Work.FIPlan.gBox R, ‖c z‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by rw [hG]; exact Finset.filter_subset _ _) (fun z _ _ => by positivity)

/-! ## The two elementary weight sums over region I -/

/-- **The `1/(b²e)` weight sum over region I.**  The region condition only shrinks the index set, so
the sum is at most the product sum, which factors into `Σ_b 1/b² ≤ 2` and `Σ_e 1/e ≤ 1 + log X`. -/
theorem regionLow_inv_sq_e_sum_le (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ) (hX : 1 ≤ X) :
    ∑ p ∈ ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
        (fun p => 4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁),
      (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ)) ≤ 4 * Real.log ((X : ℝ) + 2) := by
  classical
  set T : Finset (ℕ × ℕ) := (Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X) with hT
  have hsum : ∑ p ∈ T, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ))
      = (∑ b ∈ Finset.Icc 1 (uniB Pa), (1 : ℝ) / (b : ℝ) ^ 2)
        * (∑ e ∈ Finset.Icc 1 X, (1 : ℝ) / (e : ℝ)) := by
    rw [hT, Finset.product_eq_sprod, Finset.sum_product]
    have hinner : ∀ b ∈ Finset.Icc 1 (uniB Pa),
        (∑ e ∈ Finset.Icc 1 X, (1 : ℝ) / ((b : ℝ) ^ 2 * (e : ℝ)))
          = (1 : ℝ) / (b : ℝ) ^ 2 * (∑ e ∈ Finset.Icc 1 X, (1 : ℝ) / (e : ℝ)) := by
      intro b _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ => by rw [one_div, one_div, one_div, mul_inv])
    rw [Finset.sum_congr rfl hinner, Finset.sum_mul]
  have hb : (∑ b ∈ Finset.Icc 1 (uniB Pa), (1 : ℝ) / (b : ℝ) ^ 2) ≤ 2 :=
    Work.FIArea7.sum_inv_sq_Icc_le_two (uniB Pa)
  have he : (∑ e ∈ Finset.Icc 1 X, (1 : ℝ) / (e : ℝ)) ≤ 1 + Real.log X := by
    have h := harmonic_le_one_add_log X
    rw [harmonic_eq_sum_Icc] at h
    simpa [one_div] using h
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog : 1 + Real.log (X : ℝ) ≤ 2 * Real.log ((X : ℝ) + 2) := by
    have h1 : Real.log (X : ℝ) ≤ Real.log ((X : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3 : (3 : ℝ) ≤ (X : ℝ) + 2 := by linarith
    have hlog3 : 1 ≤ Real.log 3 := by
      have := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
      rwa [Real.log_exp] at this
    have h4 : Real.log 3 ≤ Real.log ((X : ℝ) + 2) := Real.log_le_log (by norm_num) h3
    linarith
  calc ∑ p ∈ ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
          (fun p => 4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁),
        (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ))
      ≤ ∑ p ∈ T, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (by rw [hT]; exact Finset.filter_subset _ _)
          (fun p _ _ => by positivity)
    _ = (∑ b ∈ Finset.Icc 1 (uniB Pa), (1 : ℝ) / (b : ℝ) ^ 2)
        * (∑ e ∈ Finset.Icc 1 X, (1 : ℝ) / (e : ℝ)) := hsum
    _ ≤ 2 * (1 + Real.log (X : ℝ)) :=
        mul_le_mul hb he (Finset.sum_nonneg (fun e _ => by positivity)) (by norm_num)
    _ ≤ 4 * Real.log ((X : ℝ) + 2) := by linarith

/-- **The `e` weight sum over region I.**  For a fixed `e ≥ 1` at most `N^{δ₁}/(4e(2K+L₀+2))` values
of `b` are admissible, so the contribution of each `e` is at most `N^{δ₁}/(4(2K+L₀+2)) ≤ N^{δ₁}`,
and there are at most `X ≤ X²` values of `e`. -/
theorem regionLow_e_sum_le (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ) (hX : 1 ≤ X) :
    ∑ p ∈ ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
        (fun p => 4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁),
      (p.2 : ℝ) ≤ (X : ℝ) ^ 2 * Pa.N ^ δ₁ := by
  classical
  set A : ℝ := Pa.N ^ δ₁ with hA
  set D : ℝ := 4 * (2 * (K : ℝ) + (L₀ : ℝ) + 2) with hD
  have hD8 : 8 ≤ D := by
    rw [hD]
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hL0 : (0 : ℝ) ≤ (L₀ : ℝ) := Nat.cast_nonneg L₀
    linarith
  have hDpos : 0 < D := by linarith
  have hA0 : 0 ≤ A := by
    rw [hA]; exact Real.rpow_nonneg (by linarith [Pa.hN1] : (0 : ℝ) ≤ Pa.N) δ₁
  have hfib : ∀ e : ℕ, e ∈ Finset.Icc 1 X →
      ((((Finset.Icc 1 (uniB Pa)).filter (fun b : ℕ => D * (b : ℝ) * (e : ℝ) ≤ A)).card : ℝ))
        ≤ A / D := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have he1' : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he1
    have hepos : 0 < (e : ℝ) := by linarith
    have hsub : (Finset.Icc 1 (uniB Pa)).filter (fun b : ℕ => D * (b : ℝ) * (e : ℝ) ≤ A)
        ⊆ Finset.Icc 1 (Nat.floor (A / (D * (e : ℝ)))) := by
      intro b hb
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      obtain ⟨⟨hb1, _⟩, hbc⟩ := hb
      rw [Finset.mem_Icc]
      refine ⟨hb1, ?_⟩
      have hble : (b : ℝ) ≤ A / (D * (e : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        calc (b : ℝ) * (D * (e : ℝ)) = D * (b : ℝ) * (e : ℝ) := by ring
          _ ≤ A := hbc
      exact Nat.le_floor hble
    calc ((((Finset.Icc 1 (uniB Pa)).filter (fun b : ℕ => D * (b : ℝ) * (e : ℝ) ≤ A)).card : ℝ))
        ≤ ((Finset.Icc 1 (Nat.floor (A / (D * (e : ℝ))))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.floor (A / (D * (e : ℝ))) : ℝ) := by rw [Nat.card_Icc]; simp
      _ ≤ A / (D * (e : ℝ)) := Nat.floor_le (by positivity)
      _ ≤ A / D := by
          apply div_le_div_of_nonneg_left hA0 hDpos
          nlinarith [he1', hDpos]
  have hstep : ∑ p ∈ ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
          (fun p => D * (p.1 : ℝ) * (p.2 : ℝ) ≤ A), (p.2 : ℝ)
      = ∑ e ∈ Finset.Icc 1 X,
          (e : ℝ) * ((((Finset.Icc 1 (uniB Pa)).filter
            (fun b : ℕ => D * (b : ℝ) * (e : ℝ) ≤ A)).card : ℝ)) := by
    rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_comm]
    dsimp only
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hS_eq : ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
        (fun p : ℕ × ℕ => 4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁)
      = ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
        (fun p : ℕ × ℕ => D * (p.1 : ℝ) * (p.2 : ℝ) ≤ A) := by
    apply Finset.filter_congr
    intro p _
    have h1 : 4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2)
        = D * (p.1 : ℝ) * (p.2 : ℝ) := by rw [hD]; ring
    rw [← hA, h1]
  rw [hS_eq]
  calc ∑ p ∈ ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
          (fun p : ℕ × ℕ => D * (p.1 : ℝ) * (p.2 : ℝ) ≤ A), (p.2 : ℝ)
      = ∑ e ∈ Finset.Icc 1 X,
          (e : ℝ) * ((((Finset.Icc 1 (uniB Pa)).filter
            (fun b : ℕ => D * (b : ℝ) * (e : ℝ) ≤ A)).card : ℝ)) := hstep
    _ ≤ ∑ e ∈ Finset.Icc 1 X, (X : ℝ) * (A / D) := by
        refine Finset.sum_le_sum (fun e he => ?_)
        have heX : (e : ℝ) ≤ (X : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp he).2
        exact mul_le_mul heX (hfib e he) (by positivity) (Nat.cast_nonneg X)
    _ = (X : ℝ) * ((X : ℝ) * (A / D)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]; simp
    _ ≤ (X : ℝ) ^ 2 * A := by
        have h1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
        have hAD : A / D ≤ A := by
          rw [div_le_iff₀ hDpos]; nlinarith [hA0, hD8]
        nlinarith [hAD, hA0, h1, (Nat.cast_nonneg X : (0 : ℝ) ≤ (X : ℝ))]
    _ = (X : ℝ) ^ 2 * Pa.N ^ δ₁ := by rw [hA]

/-! ## The pair-level orthogonality (Plancherel in the character group) -/

/-- **Plancherel for the §16 character sum**: the normalised `χ`-sum of `|S_χ|²` is the `ℓ²`-mass of
the class aggregates of the coefficient `c = unitCoeff Q (uniCoeff ε β k)`.

`S_χ = Σ_z c z χ(π z)` is the Fourier transform of the pushforward `A a = Σ_{π z = a} c z`, so
Plancherel (`sum_char_mul_star_self`) gives `Σ_χ |S_χ|² = Φ Σ_a |A a|²`.  On the units the class map
`unitClassD` is `gaussUnitOf`, and the coprimality in the aggregate is automatic from the vanishing
of `unitCoeff` off the units. -/
theorem sum_uniSChar_plancherel (Pa : Work.FITop.Params) (b e : ℕ) [NeZero (4 * b * e)]
    (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ) :
    (1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℝ)) *
        ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * b * e))) ℂ,
          ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ ^ 2
      = ∑ a : Work.FIArea7.GaussUnit (4 * b * e),
          ‖∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z => Nat.Coprime (Work.FIPlan.gnorm z) (4 * b * e)
                ∧ Work.FIArea7.unitClassD (4 * b * e) z = a),
            Work.FIArea7.unitCoeff (4 * b * e) (Work.FIArea7.uniCoeff ε β k) z‖ ^ 2 := by
  classical
  set Q : ℕ := 4 * b * e with hQdef
  haveI : NeZero Q := by rw [hQdef]; infer_instance
  set A : Work.FIArea7.GaussUnit Q → ℂ := fun a =>
      ∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
          (fun z => Nat.Coprime (Work.FIPlan.gnorm z) Q ∧ Work.FIArea7.unitClassD Q z = a),
        Work.FIArea7.unitCoeff Q (Work.FIArea7.uniCoeff ε β k) z with hA
  have hvanish : ∀ z : GaussianInt, ¬ Nat.Coprime (Work.FIPlan.gnorm z) Q →
      Work.FIArea7.unitCoeff Q (Work.FIArea7.uniCoeff ε β k) z = 0 := by
    intro z hz
    rw [Work.FIArea7.unitCoeff, Work.FIArea7.unitInd, if_neg hz, mul_zero]
  have hAeq : ∀ a : Work.FIArea7.GaussUnit Q,
      A a = ∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
          (fun z => Work.FIArea7.unitClassD Q z = a),
        Work.FIArea7.unitCoeff Q (Work.FIArea7.uniCoeff ε β k) z := by
    intro a
    rw [hA]
    refine Finset.sum_subset ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.2⟩
    · intro z hz hzn
      rw [Finset.mem_filter] at hz
      exact hvanish z (fun hc => hzn (by rw [Finset.mem_filter]; exact ⟨hz.1, hc, hz.2⟩))
  have hS : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ,
      Work.FIArea7.uniSChar Pa Q ε β k χ
        = ∑ a : Work.FIArea7.GaussUnit Q, A a * χ (Additive.ofMul a) := by
    intro χ
    rw [Work.FIArea7.uniSChar]
    rw [← Finset.sum_fiberwise (Work.FIPlan.gBox (Work.FITop.radN Pa))
          (fun z : GaussianInt => Work.FIArea7.unitClassD Q z)
          (fun z => Work.FIArea7.unitCoeff Q (Work.FIArea7.uniCoeff ε β k) z *
            χ (Additive.ofMul (Work.FIArea7.unitClassD Q z)))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hAeq a, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [(Finset.mem_filter.mp hz).2]
  have hplanC : ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ,
        (Work.FIArea7.uniSChar Pa Q ε β k χ) * star (Work.FIArea7.uniSChar Pa Q ε β k χ)
      = (Fintype.card (Work.FIArea7.GaussUnit Q) : ℂ) * ∑ a, A a * star (A a) := by
    simp_rw [hS]
    exact Work.FIArea7.sum_char_mul_star_self (Work.FIArea7.GaussUnit Q) A
  have hplanR : ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ,
        ‖Work.FIArea7.uniSChar Pa Q ε β k χ‖ ^ 2
      = (Fintype.card (Work.FIArea7.GaussUnit Q) : ℝ) * ∑ a, ‖A a‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
    have h1 : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ,
        ((‖Work.FIArea7.uniSChar Pa Q ε β k χ‖ ^ 2 : ℝ) : ℂ)
          = Work.FIArea7.uniSChar Pa Q ε β k χ
              * star (Work.FIArea7.uniSChar Pa Q ε β k χ) :=
      fun χ => (Work.FIArea7.mul_conj_eq_ofReal_normSq _).symm
    have h2 : ∀ a : Work.FIArea7.GaussUnit Q, ((‖A a‖ ^ 2 : ℝ) : ℂ) = A a * star (A a) :=
      fun a => (Work.FIArea7.mul_conj_eq_ofReal_normSq _).symm
    simp_rw [h1, h2]
    exact hplanC
  have hcard : (Fintype.card (Work.FIArea7.GaussUnit Q) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [hplanR, hA]
  rw [one_div, inv_mul_cancel_left₀ hcard]

/-- **The pair-level orthogonality bound** for the §16 expansion: `uniModeCharSum` is bounded by the
number of rational classes (`≤ Q`) times the `ℓ²`-mass of the class aggregates. -/
theorem uniModeCharSum_pair_le_aux (Pa : Work.FITop.Params) (b e : ℕ) [NeZero (4 * b * e)]
    (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ) :
    ‖Work.FIArea7.uniModeCharSum Pa b e β k ε‖
      ≤ ((4 * b * e : ℕ) : ℝ) *
        ∑ a : Work.FIArea7.GaussUnit (4 * b * e),
          ‖∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
              (fun z => Nat.Coprime (Work.FIPlan.gnorm z) (4 * b * e)
                ∧ Work.FIArea7.unitClassD (4 * b * e) z = a),
            Work.FIArea7.unitCoeff (4 * b * e) (Work.FIArea7.uniCoeff ε β k) z‖ ^ 2 := by
  classical
  have hpl := sum_uniSChar_plancherel Pa b e β k ε
  have hnorm : ‖(1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℂ))‖
      = 1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  have hpos : (0 : ℝ) < 1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℝ) := by
    have : (0 : ℝ) < (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    positivity
  rw [Work.FIArea7.uniModeCharSum]
  calc ‖(1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℂ)) *
        ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * b * e))) ℂ,
          Work.FIArea7.uniJChar (4 * b * e) e χ *
          (Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ) *
          star (Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ)‖
      = (1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℝ)) *
        ‖∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * b * e))) ℂ,
          Work.FIArea7.uniJChar (4 * b * e) e χ *
          (Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ) *
          star (Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ)‖ := by
        rw [norm_mul, hnorm]
    _ ≤ (1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℝ)) *
        ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * b * e))) ℂ,
          ‖Work.FIArea7.uniJChar (4 * b * e) e χ *
          (Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ) *
          star (Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (le_of_lt hpos)
    _ ≤ (1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℝ)) *
        ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * b * e))) ℂ,
          ((4 * b * e : ℕ) : ℝ) *
          ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => ?_)) (le_of_lt hpos)
        have hJ := Work.FIArea7.norm_ratWeight_charSum_le (4 * b * e) e χ
        have hs0 : (0 : ℝ) ≤ ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ := norm_nonneg _
        calc ‖Work.FIArea7.uniJChar (4 * b * e) e χ *
              (Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ) *
              star (Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ)‖
            = ‖Work.FIArea7.uniJChar (4 * b * e) e χ‖ *
              ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ *
              ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ := by
              rw [norm_mul, norm_mul, norm_star]
          _ ≤ ((4 * b * e : ℕ) : ℝ) *
              ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ *
              ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJ hs0) hs0
          _ = ((4 * b * e : ℕ) : ℝ) *
              ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ ^ 2 := by ring
    _ = ((4 * b * e : ℕ) : ℝ) *
          ((1 / (Fintype.card (Work.FIArea7.GaussUnit (4 * b * e)) : ℝ)) *
            ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * b * e))) ℂ,
              ‖Work.FIArea7.uniSChar Pa (4 * b * e) ε β k χ‖ ^ 2) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun χ _ => by ring)
    _ = ((4 * b * e : ℕ) : ℝ) *
          ∑ a : Work.FIArea7.GaussUnit (4 * b * e),
            ‖∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
                (fun z => Nat.Coprime (Work.FIPlan.gnorm z) (4 * b * e)
                  ∧ Work.FIArea7.unitClassD (4 * b * e) z = a),
              Work.FIArea7.unitCoeff (4 * b * e) (Work.FIArea7.uniCoeff ε β k) z‖ ^ 2 := by
        rw [hpl]

/-! ## Norm bounds and the shape of `radN` -/

/-- `‖(z/|z|)^k‖ ≤ 1` for every `z` (including `z = 0`). -/
theorem norm_uniPow_le_one_aux (z : GaussianInt) (k : ℤ) : ‖Work.FIArea7.uniPow z k‖ ≤ 1 := by
  rw [Work.FIArea7.uniPow]
  by_cases hz : z.toComplex = 0
  · rw [hz, zero_div, norm_zpow, norm_zero, zero_zpow_eq]
    split <;> norm_num
  · rw [norm_zpow]
    have hnorm : ‖z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hz)]
    rw [hnorm, one_zpow]

/-- `‖uniCoeff ε β k z‖ ≤ ‖β z‖` when `|ε z| ≤ 1`. -/
theorem uniCoeff_norm_le_aux (ε : GaussianInt → ℤ) (β : GaussianInt → ℂ) (k : ℤ)
    (hε : ∀ z : GaussianInt, |(ε z : ℝ)| ≤ 1) (z : GaussianInt) :
    ‖Work.FIArea7.uniCoeff ε β k z‖ ≤ ‖β z‖ := by
  have h1 : ‖(((ε z : ℤ)) : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_intCast] using hε z
  rw [Work.FIArea7.uniCoeff, norm_mul, norm_mul]
  calc ‖(((ε z : ℤ)) : ℂ)‖ * ‖Work.FIArea7.betaPrime β z‖ * ‖Work.FIArea7.uniPow z k‖
      ≤ 1 * ‖β z‖ * 1 := by
        apply mul_le_mul
        · exact mul_le_mul h1 (Work.FIArea7.norm_betaPrime_le β z) (norm_nonneg _) (by norm_num)
        · exact norm_uniPow_le_one_aux z k
        · positivity
        · positivity
    _ = ‖β z‖ := by ring

/-- The box radius of `radN` is what it should be: `(2·radN Pa + 1)² ≤ 49 N`. -/
theorem radN_sq_le (Pa : Work.FITop.Params) :
    (((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ) ^ 2 ≤ 49 * Pa.N := by
  set R : ℕ := ⌈Real.sqrt (4 * Pa.N)⌉₊ with hR
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hradN : Work.FITop.radN Pa = (R : ℤ) := by rw [Work.FITop.radN, hR]
  have htoNat : (2 * Work.FITop.radN Pa + 1).toNat = 2 * R + 1 := by
    have h2 : (2 * Work.FITop.radN Pa + 1 : ℤ) = ((2 * R + 1 : ℕ) : ℤ) := by
      rw [hradN]; push_cast; ring
    rw [h2, Int.toNat_natCast]
  rw [htoNat]
  have hsqrt4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt 4 = 2 from by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
  have hRlt : (R : ℝ) < 2 * Real.sqrt Pa.N + 1 := by
    rw [hR, ← hsqrt4]; exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hle : (2 * (R : ℝ) + 1) ≤ 4 * Real.sqrt Pa.N + 3 := by linarith
  have hsqN : (Real.sqrt Pa.N) ^ 2 = Pa.N := Real.sq_sqrt hN0
  have hsqrtle : Real.sqrt Pa.N ≤ Pa.N := by nlinarith [hsqN, Real.sqrt_nonneg Pa.N, hN1]
  calc (((2 * R + 1 : ℕ) : ℝ)) ^ 2 = (2 * (R : ℝ) + 1) ^ 2 := by push_cast; ring
    _ ≤ (4 * Real.sqrt Pa.N + 3) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
    _ ≤ 49 * Pa.N := by nlinarith [hsqN, hsqrtle, hN1]

/-! ## The per-`(b,e)`, per-`k` sharp bound on the mode char sum -/

/-- **The pair-level sharp bound for a single mode.**  Combining the orthogonality bound
`uniModeCharSum_pair_le_aux` with the honest class count `classAggregate_le` and the elementary
`(2R+1)² ≤ 49N` gives, uniformly in `k`,

  `‖uniModeCharSum Pa b e β k ε‖ ≤ (98N/(4be) + 2·4be)·Σ_{z ∈ gBox radN}‖β z‖²`.

Neither Proposition 17.2 nor the region condition is used: this is the whole point of the pair
route. -/
theorem uniModeCharSum_pair_sharp_le (Pa : Work.FITop.Params) (b e : ℕ) [NeZero (4 * b * e)]
    (hb : 1 ≤ b) (he : 1 ≤ e)
    (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ) (hε : ∀ z : GaussianInt, |(ε z : ℝ)| ≤ 1) :
    ‖Work.FIArea7.uniModeCharSum Pa b e β k ε‖
      ≤ (98 * (Pa.N : ℝ) / (4 * (b : ℝ) * (e : ℝ)) + 2 * (4 * (b : ℝ) * (e : ℝ)))
          * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2) := by
  classical
  have hb0 : 0 < b := hb
  have he0 : 0 < e := he
  have hcast : ((4 * b * e : ℕ) : ℝ) = 4 * (b : ℝ) * (e : ℝ) := by push_cast; ring
  set E : ℝ := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hQ0 : (0 : ℝ) < ((4 * b * e : ℕ) : ℝ) := by
    have : (0 : ℕ) < 4 * b * e := by positivity
    exact_mod_cast this
  -- the class aggregate bound
  have h2 : ∑ a : Work.FIArea7.GaussUnit (4 * b * e),
        ‖∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
            (fun z => Nat.Coprime (Work.FIPlan.gnorm z) (4 * b * e)
              ∧ Work.FIArea7.unitClassD (4 * b * e) z = a),
          Work.FIArea7.unitCoeff (4 * b * e) (Work.FIArea7.uniCoeff ε β k) z‖ ^ 2
      ≤ ((((2 * Work.FITop.radN Pa + 1).toNat / (4 * b * e) + 1) ^ 2 : ℕ) : ℝ) * E := by
    refine le_trans (classAggregate_le (4 * b * e) (Work.FITop.radN Pa)
      (Work.FIArea7.unitCoeff (4 * b * e) (Work.FIArea7.uniCoeff ε β k))) ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hE]
    refine Finset.sum_le_sum (fun z _ => ?_)
    have hind : ‖Work.FIArea7.unitInd (4 * b * e) z‖ ≤ 1 := by
      rw [Work.FIArea7.unitInd]; split <;> simp
    have hc : ‖Work.FIArea7.unitCoeff (4 * b * e) (Work.FIArea7.uniCoeff ε β k) z‖
        ≤ ‖Work.FIArea7.uniCoeff ε β k z‖ := by
      rw [Work.FIArea7.unitCoeff, norm_mul]
      calc ‖star (Work.FIArea7.uniCoeff ε β k z)‖ * ‖Work.FIArea7.unitInd (4 * b * e) z‖
          ≤ ‖Work.FIArea7.uniCoeff ε β k z‖ * 1 :=
            mul_le_mul (le_of_eq (norm_star _)) hind (norm_nonneg _) (norm_nonneg _)
        _ = ‖Work.FIArea7.uniCoeff ε β k z‖ := by ring
    exact pow_le_pow_left₀ (norm_nonneg _) (le_trans hc (uniCoeff_norm_le_aux ε β k hε z)) 2
  -- the arithmetic `Q·F ≤ 98N/Q + 2Q`
  have hQF : ((4 * b * e : ℕ) : ℝ)
        * ((((2 * Work.FITop.radN Pa + 1).toNat / (4 * b * e) + 1) ^ 2 : ℕ) : ℝ)
      ≤ 98 * (Pa.N : ℝ) / ((4 * b * e : ℕ) : ℝ) + 2 * ((4 * b * e : ℕ) : ℝ) := by
    have hm2 : ((((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ)) ^ 2 ≤ 49 * Pa.N := radN_sq_le Pa
    have hstep1 : ((((2 * Work.FITop.radN Pa + 1).toNat / (4 * b * e) + 1) ^ 2 : ℕ) : ℝ)
        ≤ (((((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ) / ((4 * b * e : ℕ) : ℝ)) + 1) ^ 2 := by
      have h5 : ((((2 * Work.FITop.radN Pa + 1).toNat / (4 * b * e) + 1 : ℕ)) : ℝ)
          ≤ ((((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ) / ((4 * b * e : ℕ) : ℝ)) + 1 := by
        have h6 : ((((2 * Work.FITop.radN Pa + 1).toNat / (4 * b * e) : ℕ)) : ℝ)
            ≤ ((((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ)) / ((4 * b * e : ℕ) : ℝ) :=
          Nat.cast_div_le
        push_cast at h6 ⊢
        linarith [h6]
      push_cast at h5 ⊢
      exact pow_le_pow_left₀ (by positivity) h5 2
    have hstep2 : (((((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ) / ((4 * b * e : ℕ) : ℝ)) + 1) ^ 2
        ≤ 2 * (((((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ) / ((4 * b * e : ℕ) : ℝ))) ^ 2 + 2 := by
      nlinarith [sq_nonneg (((((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ) / ((4 * b * e : ℕ) : ℝ)) - 1)]
    calc ((4 * b * e : ℕ) : ℝ)
          * ((((2 * Work.FITop.radN Pa + 1).toNat / (4 * b * e) + 1) ^ 2 : ℕ) : ℝ)
        ≤ ((4 * b * e : ℕ) : ℝ) * (2 * (((((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ)
            / ((4 * b * e : ℕ) : ℝ))) ^ 2 + 2) := by
          exact mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) (le_of_lt hQ0)
      _ = 2 * ((((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ)) ^ 2 / ((4 * b * e : ℕ) : ℝ)
            + 2 * ((4 * b * e : ℕ) : ℝ) := by
          field_simp
          try ring
      _ ≤ 2 * (49 * Pa.N) / ((4 * b * e : ℕ) : ℝ) + 2 * ((4 * b * e : ℕ) : ℝ) := by
          apply add_le_add
          · apply div_le_div_of_nonneg_right _ (le_of_lt hQ0)
            linarith
          · exact le_refl _
      _ = 98 * (Pa.N : ℝ) / ((4 * b * e : ℕ) : ℝ) + 2 * ((4 * b * e : ℕ) : ℝ) := by ring
  calc ‖Work.FIArea7.uniModeCharSum Pa b e β k ε‖
      ≤ ((4 * b * e : ℕ) : ℝ) *
          ∑ a : Work.FIArea7.GaussUnit (4 * b * e),
            ‖∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
                (fun z => Nat.Coprime (Work.FIPlan.gnorm z) (4 * b * e)
                  ∧ Work.FIArea7.unitClassD (4 * b * e) z = a),
              Work.FIArea7.unitCoeff (4 * b * e) (Work.FIArea7.uniCoeff ε β k) z‖ ^ 2 :=
        uniModeCharSum_pair_le_aux Pa b e β k ε
    _ ≤ ((4 * b * e : ℕ) : ℝ) * ((((((2 * Work.FITop.radN Pa + 1).toNat / (4 * b * e) + 1) ^ 2 : ℕ)) : ℝ) * E) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((4 * b * e : ℕ) : ℝ) * ((((2 * Work.FITop.radN Pa + 1).toNat / (4 * b * e) + 1) ^ 2 : ℕ) : ℝ) * E := by ring
    _ ≤ (98 * (Pa.N : ℝ) / ((4 * b * e : ℕ) : ℝ) + 2 * ((4 * b * e : ℕ) : ℝ)) * E :=
        mul_le_mul_of_nonneg_right hQF hE0
    _ = (98 * (Pa.N : ℝ) / (4 * (b : ℝ) * (e : ℝ)) + 2 * (4 * (b : ℝ) * (e : ℝ))) * E := by
        rw [hcast]

/-! ## The main theorem -/


/-- **A6: the (17.10) orthogonality at the pair level, with the *honest* class count.**
This replaces the crude `charRegionLow_pair_le` (which loses a whole factor `X` — fatal for the
`δτ` term) on the path of `AREA7_ROUTE_LEAD.md` §2.2.  It is *not* a deep-input lemma: it bounds the
region-I character sum of an arbitrary coefficient `v` by its `ℓ²`-mass.

Proof: per `(b,e)`, with `Q = 4be ≤ N^{δ₁}`:
1. `‖(1/Φ)Σ_χ J(χ)|S_χ(v)|²‖ ≤ max|J|·Σ_{a mod Q}‖Σ_{z ≡ a (Q)} v_z‖²`;
2. `max|J| ≤ #rational classes ≤ Q`, since `|ratWeight| ≤ 1`;
3. `#{z ∈ gBox R : z ≡ a (Q)} ≤ ((2R+1)/Q + 1)² ≤ 2(25N/Q² + 1)`, so each term is
   `≤ ‖v‖²(50N/Q + 2Q)`;
4. sum with the Möbius weight `(1/b)·H_K`: `Σ 1/(b·be) ≤ 2·log(X+2)` and
   `Σ (1/b)·be ≤ X²·N^{δ₁}` (the region is `4be(2K+L₀+2) ≤ N^{δ₁}`). -/
theorem charRegionLow_pair_sharp_le : ∃ C : ℝ, 0 < C ∧
  ∀ {Pa : Work.FITop.Params} {X K L₀ : ℕ} {δ₁ : ℝ} (v : GaussianInt → ℂ) (ε : GaussianInt → ℤ),
    1 ≤ X → 1 ≤ K → 0 < δ₁ → (∀ z, |(ε z : ℝ)| ≤ 1) →
    ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ v ε‖
      ≤ C * (Real.log ((K:ℝ) + 2)) ^ 2 * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2)
          * (Pa.N * Real.log ((X:ℝ) + 2) + (X:ℝ) ^ 2 * Pa.N ^ δ₁) := by
  refine ⟨10000, by norm_num, ?_⟩
  intro Pa X K L₀ δ₁ v ε hX hK hδ hε
  classical
  set S : Finset (ℕ × ℕ) :=
      ((Finset.Icc 1 (Work.FIArea7.uniB Pa)).product (Finset.Icc 1 X)).filter
        (fun p => 4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁)
    with hS
  set E : ℝ := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2 with hE
  set H : ℝ := 2 * Real.log 2 + Real.log 4
      + ∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ)) with hH
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by linarith
  have hA0 : 0 ≤ Pa.N ^ δ₁ := Real.rpow_nonneg hN0 δ₁
  have hlog3 : 1 ≤ Real.log 3 := by
    have := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
    rwa [Real.log_exp] at this
  have hlogX1 : 1 ≤ Real.log ((X : ℝ) + 2) :=
    le_trans hlog3 (Real.log_le_log (by norm_num) (by linarith))
  have hlogX0 : 0 ≤ Real.log ((X : ℝ) + 2) := le_trans zero_le_one hlogX1
  have hlogK1 : 1 ≤ Real.log ((K : ℝ) + 2) := by
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    exact le_trans hlog3 (Real.log_le_log (by norm_num) (by linarith))
  have hlogK0 : 0 ≤ Real.log ((K : ℝ) + 2) := le_trans zero_le_one hlogK1
  -- the mode weight `H`
  have hH0 : 0 ≤ H := by
    rw [hH]
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h3 : 0 ≤ ∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ)) := by
      refine Finset.sum_nonneg (fun k hk => ?_)
      have hk0 : k ≠ 0 := by
        rw [Work.FIArea7.evenFreq, Finset.mem_filter] at hk; exact hk.2.1
      have hkpos : (0 : ℤ) < |k| := abs_pos.mpr hk0
      have hkposR : (0 : ℝ) < ((|k| : ℤ) : ℝ) := by exact_mod_cast hkpos
      positivity
    linarith
  have hH25 : H ≤ 25 * Real.log ((K : ℝ) + 2) := by
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; norm_num
    have hsum := Work.FIArea7.sum_inv_abs_evenFreq_le K
    have hlogm : Real.log (2 * (K : ℝ) + 2) = Real.log 2 + Real.log ((K : ℝ) + 1) := by
      rw [show (2 * (K : ℝ) + 2) = 2 * ((K : ℝ) + 1) from by ring,
        Real.log_mul (by norm_num) (by positivity)]
    rw [hlogm] at hsum
    have hlogK : Real.log ((K : ℝ) + 1) ≤ Real.log ((K : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog2le1 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hlogle : Real.log 2 ≤ Real.log ((K : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) K])
    rw [hH, hlog4]
    nlinarith [hsum, hlogK, hlog2le1, hlogle, hlogK1]
  -- the per-`(b,e)` bound
  have hterm : ∀ p ∈ S, ‖Work.FIArea7.uniCharTerm Pa p.1 p.2 v K ε‖
      ≤ (1 / (p.1 : ℝ)) * H * ((98 * (Pa.N : ℝ) / (4 * (p.1 : ℝ) * (p.2 : ℝ))
            + 2 * (4 * (p.1 : ℝ) * (p.2 : ℝ))) * E) := by
    intro p hp
    rw [hS] at hp
    obtain ⟨hpT, hpred⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpT
    have hb : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
    have he : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
    have hb0 : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast (show (0 : ℕ) < p.1 by omega)
    have hbp : (0 : ℝ) < 4 * (p.1 : ℝ) * (p.2 : ℝ) := by
      have : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast he
      positivity
    have hbe : 4 * p.1 * p.2 ≠ 0 := by positivity
    haveI : NeZero (4 * p.1 * p.2) := ⟨hbe⟩
    set Bnd : ℝ := (98 * (Pa.N : ℝ) / (4 * (p.1 : ℝ) * (p.2 : ℝ))
            + 2 * (4 * (p.1 : ℝ) * (p.2 : ℝ))) * E with hBnd
    have hBnd0 : 0 ≤ Bnd := by
      rw [hBnd]
      have h2 : 0 ≤ 98 * (Pa.N : ℝ) / (4 * (p.1 : ℝ) * (p.2 : ℝ)) := by positivity
      have h3 : 0 ≤ 2 * (4 * (p.1 : ℝ) * (p.2 : ℝ)) := by positivity
      exact mul_nonneg (by linarith) hE0
    have hmode : ∀ k : ℤ, ‖Work.FIArea7.uniModeCharSum Pa p.1 p.2 v k ε‖ ≤ Bnd := by
      intro k
      have h1 := uniModeCharSum_pair_sharp_le Pa p.1 p.2 hb he v k ε hε
      rw [hBnd, hE]
      exact h1
    have hcastk : ∀ k : ℤ, ‖(1 / (|k| : ℝ) : ℂ)‖ = 1 / ((|k| : ℤ) : ℝ) := by
      intro k
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_abs, ← Int.cast_abs]
    rw [Work.FIArea7.uniCharTerm, dif_neg hbe, norm_mul]
    have hmu : ‖(((ArithmeticFunction.moebius p.1 : ℝ) / (p.1 : ℝ) : ℝ) : ℂ)‖ ≤ 1 / (p.1 : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_nonneg (show (0 : ℝ) ≤ (p.1 : ℝ) by positivity)]
      have h1 : |((ArithmeticFunction.moebius p.1 : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
      exact div_le_div_of_nonneg_right h1 (le_of_lt hb0)
    have hmain : ‖(((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ)
            * Work.FIArea7.uniModeCharSum Pa p.1 p.2 v 0 ε
          + ∑ k ∈ Work.FIArea7.evenFreq K,
              (1 / (|k| : ℝ) : ℂ) * Work.FIArea7.uniModeCharSum Pa p.1 p.2 v k ε‖
        ≤ H * Bnd := by
      refine le_trans (norm_add_le _ _) ?_
      have h1 : ‖(((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ)
            * Work.FIArea7.uniModeCharSum Pa p.1 p.2 v 0 ε‖
          ≤ (2 * Real.log 2 + Real.log 4) * Bnd := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hmode 0) (by positivity)
      have h2 : ‖∑ k ∈ Work.FIArea7.evenFreq K,
            (1 / (|k| : ℝ) : ℂ) * Work.FIArea7.uniModeCharSum Pa p.1 p.2 v k ε‖
          ≤ (∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ))) * Bnd := by
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ k ∈ Work.FIArea7.evenFreq K,
              ‖(1 / (|k| : ℝ) : ℂ) * Work.FIArea7.uniModeCharSum Pa p.1 p.2 v k ε‖
            ≤ ∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ)) * Bnd := by
              refine Finset.sum_le_sum (fun k _ => ?_)
              rw [norm_mul, hcastk k]
              exact mul_le_mul_of_nonneg_left (hmode k) (by positivity)
          _ = (∑ k ∈ Work.FIArea7.evenFreq K, (1 / ((|k| : ℤ) : ℝ))) * Bnd := by
              rw [Finset.sum_mul]
      rw [hH]
      linarith
    exact le_trans (mul_le_mul hmu hmain (norm_nonneg _) (by positivity))
      (le_of_eq (by ring))
  -- the two weight sums
  have hkey : ∀ p ∈ S, (1 / (p.1 : ℝ)) * ((98 * (Pa.N : ℝ) / (4 * (p.1 : ℝ) * (p.2 : ℝ))
        + 2 * (4 * (p.1 : ℝ) * (p.2 : ℝ))))
      = 98 * (Pa.N : ℝ) / 4 * ((1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ))) + 8 * (p.2 : ℝ) := by
    intro p hp
    rw [hS] at hp
    obtain ⟨hpT, hpred⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpT
    have hb : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
    have he : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
    have hb1 : (p.1 : ℝ) ≠ 0 := by positivity
    have he1 : (p.2 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hW1 : 0 ≤ 98 * (Pa.N : ℝ) * Real.log ((X : ℝ) + 2) + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁) := by
    nlinarith [mul_nonneg hN0 hlogX0, mul_nonneg (sq_nonneg (X : ℝ)) hA0]
  have hW2 : 0 ≤ Pa.N * Real.log ((X : ℝ) + 2) + (X : ℝ) ^ 2 * Pa.N ^ δ₁ := by
    nlinarith [mul_nonneg hN0 hlogX0, mul_nonneg (sq_nonneg (X : ℝ)) hA0]
  have hwsum : ∑ p ∈ S, (1 / (p.1 : ℝ)) * ((98 * (Pa.N : ℝ) / (4 * (p.1 : ℝ) * (p.2 : ℝ))
        + 2 * (4 * (p.1 : ℝ) * (p.2 : ℝ))))
      ≤ 98 * (Pa.N : ℝ) * Real.log ((X : ℝ) + 2) + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁) := by
    calc ∑ p ∈ S, (1 / (p.1 : ℝ)) * ((98 * (Pa.N : ℝ) / (4 * (p.1 : ℝ) * (p.2 : ℝ))
          + 2 * (4 * (p.1 : ℝ) * (p.2 : ℝ))))
        = ∑ p ∈ S, (98 * (Pa.N : ℝ) / 4 * ((1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ)))
            + 8 * (p.2 : ℝ)) := Finset.sum_congr rfl (fun p hp => hkey p hp)
      _ = 98 * (Pa.N : ℝ) / 4 * (∑ p ∈ S, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ)))
            + 8 * (∑ p ∈ S, (p.2 : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 98 * (Pa.N : ℝ) / 4 * (4 * Real.log ((X : ℝ) + 2)) + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (regionLow_inv_sq_e_sum_le Pa X K L₀ δ₁ hX)
              (by positivity)
          · exact mul_le_mul_of_nonneg_left (regionLow_e_sum_le Pa X K L₀ δ₁ hX) (by norm_num)
      _ = 98 * (Pa.N : ℝ) * Real.log ((X : ℝ) + 2) + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁) := by ring
  -- the assembly
  have hchar : ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ v ε‖
      ≤ 2 * ∑ p ∈ S, ‖Work.FIArea7.uniCharTerm Pa p.1 p.2 v K ε‖ := by
    rw [Work.FIArea7.charRegionLow6, ← hS, norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
  have hstep1 : (2 : ℝ) * ∑ p ∈ S, ‖Work.FIArea7.uniCharTerm Pa p.1 p.2 v K ε‖
      ≤ 2 * ∑ p ∈ S, (1 / (p.1 : ℝ)) * H * ((98 * (Pa.N : ℝ) / (4 * (p.1 : ℝ) * (p.2 : ℝ))
            + 2 * (4 * (p.1 : ℝ) * (p.2 : ℝ))) * E) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
  have hfin1 : 2 * H ≤ 50 * (Real.log ((K : ℝ) + 2)) ^ 2 := by
    nlinarith [hH25, hH0, hlogK1, sq_nonneg (Real.log ((K : ℝ) + 2))]
  have hfin2 : 50 * (98 * (Pa.N : ℝ) * Real.log ((X : ℝ) + 2) + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁))
      ≤ 10000 * (Pa.N * Real.log ((X : ℝ) + 2) + (X : ℝ) ^ 2 * Pa.N ^ δ₁) := by
    nlinarith [mul_nonneg hN0 hlogX0, mul_nonneg (sq_nonneg (X : ℝ)) hA0]
  calc ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ v ε‖
      ≤ 2 * ∑ p ∈ S, ‖Work.FIArea7.uniCharTerm Pa p.1 p.2 v K ε‖ := hchar
    _ ≤ 2 * ∑ p ∈ S, (1 / (p.1 : ℝ)) * H * ((98 * (Pa.N : ℝ) / (4 * (p.1 : ℝ) * (p.2 : ℝ))
            + 2 * (4 * (p.1 : ℝ) * (p.2 : ℝ))) * E) := hstep1
    _ = 2 * H * E * (∑ p ∈ S, (1 / (p.1 : ℝ)) * (98 * (Pa.N : ℝ) / (4 * (p.1 : ℝ) * (p.2 : ℝ))
            + 2 * (4 * (p.1 : ℝ) * (p.2 : ℝ)))) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ ≤ 2 * H * E * (98 * (Pa.N : ℝ) * Real.log ((X : ℝ) + 2)
            + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁)) :=
        mul_le_mul_of_nonneg_left hwsum (by positivity)
    _ = (2 * H) * E * (98 * (Pa.N : ℝ) * Real.log ((X : ℝ) + 2)
            + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁)) := by ring
    _ ≤ (50 * (Real.log ((K : ℝ) + 2)) ^ 2) * E
          * (98 * (Pa.N : ℝ) * Real.log ((X : ℝ) + 2)
            + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁)) := by
        apply mul_le_mul_of_nonneg_right _ hW1
        apply mul_le_mul_of_nonneg_right hfin1 hE0
    _ ≤ 10000 * (Real.log ((K : ℝ) + 2)) ^ 2 * E
          * (Pa.N * Real.log ((X : ℝ) + 2) + (X : ℝ) ^ 2 * Pa.N ^ δ₁) := by
        have h1 : (50 * (Real.log ((K : ℝ) + 2)) ^ 2) * E
              * (98 * (Pa.N : ℝ) * Real.log ((X : ℝ) + 2) + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁))
            = ((Real.log ((K : ℝ) + 2)) ^ 2 * E)
              * (50 * (98 * (Pa.N : ℝ) * Real.log ((X : ℝ) + 2)
                + 8 * ((X : ℝ) ^ 2 * Pa.N ^ δ₁))) := by ring
        rw [h1]
        refine le_trans (mul_le_mul_of_nonneg_left hfin2 (by positivity)) (le_of_eq ?_)
        ring

end Work.FIArea7
