import Mathlib
import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.Saddle.linking_no_escape
import Submission.Work.RPCore.Saddle.exists_descent_isotopy
import Submission.Work.RPCore.Saddle.exists_delta_le_fderiv
import Submission.Work.RPCore.Saddle.saddle_linking_point

/-!
# `Work.RPCore.Saddle.exists_crit_of_saddle_split`

A saddle-point existence theorem: a `C²` function on `ℝ × (ℝ^k × ℝ^l)`, periodic in the first
variable, which is a bounded perturbation of the quadratic form `(⟨A₁x,x⟩ + ⟨A₂y,y⟩)/2` with `A₁`
negative definite and `A₂` positive definite, has a critical point.

The proof is the classical **mountain-pass / linking** argument.  Writing `D^k` for the closed unit
ball of `ℝ^k` and `γ₀ u = (a₀, (ρu, 0))` for the embedding of its boundary sphere, let

`c = inf { t | ∃ γ : D^k → ℝ × (ℝ^k × ℝ^l), γ continuous, γ = γ₀ on ∂D^k, ∀ u, F (γ u) ≤ t }`

be the min-max level.  Assuming `F` has no critical point, its gradient is bounded below by some
`δ > 0` (`exists_delta_le_fderiv`), and the "linking" lemma (`saddle_linking_point`, i.e. no
retraction of the ball onto its sphere) gives that every such `γ` meets `{x = 0}`, where
`F ≥ -C`; hence `-C ≤ c ≤ C`.  Choosing `ρ` large, the boundary sphere sits in a neighbourhood `U`
on which `F ≤ c' < c`.  The cut-off negative-gradient isotopy `exists_descent_isotopy` fixes `U`
and pushes `F` strictly below `c` on the image of a near-minimising `γ`, contradicting the
definition of `c`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open scoped Topology
open Filter

namespace Work.RPCore.Saddle

theorem exists_crit_of_saddle_split {k l : ℕ}
    (F : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) → ℝ)
    (hF : ContDiff ℝ 2 F) (Pd : ℝ) (hPd : 0 < Pd)
    (hper : ∀ a v, F (a + Pd, v) = F (a, v))
    (A₁ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (A₂ : EuclideanSpace ℝ (Fin l) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (lam K C : ℝ) (hlam : 0 < lam) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA₁ : ∀ x, inner ℝ (A₁ x) x ≤ -lam * ‖x‖ ^ 2) (hA₁' : ∀ x, ‖A₁ x‖ ≤ K * ‖x‖)
    (hA₂ : ∀ y, lam * ‖y‖ ^ 2 ≤ inner ℝ (A₂ y) y) (hA₂' : ∀ y, ‖A₂ y‖ ≤ K * ‖y‖)
    (hC0 : ∀ a v, |F (a, v) - (inner ℝ (A₁ v.1) v.1 + inner ℝ (A₂ v.2) v.2) / 2| ≤ C)
    (hC1 : ∀ a v w, |fderiv ℝ F (a, v) w - (inner ℝ (A₁ v.1) w.2.1 + inner ℝ (A₂ v.2) w.2.2)| ≤ C * ‖w‖) :
    ∃ z, fderiv ℝ F z = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨δ, hδpos, hδF⟩ := exists_delta_le_fderiv F (hF.of_le (by norm_num)) Pd hPd hper
    A₁ A₂ lam C hlam hC hA₁ hA₂ hC1 hcon
  -- A bound used several times: `F` at `x = 0` is at least `-C`.
  have hzero_le : ∀ (a : ℝ) (y : EuclideanSpace ℝ (Fin l)), -C ≤ F (a, (0, y)) := by
    intro a y
    have h2 := (abs_le.mp (hC0 a ((0 : EuclideanSpace ℝ (Fin k)), y))).1
    have hinner : inner ℝ (A₁ (0 : EuclideanSpace ℝ (Fin k)))
        (0 : EuclideanSpace ℝ (Fin k)) = 0 := by simp
    rw [hinner, zero_add] at h2
    dsimp only at h2
    have h5 := hA₂ y
    have h6 : (0:ℝ) ≤ lam * ‖y‖ ^ 2 := mul_nonneg hlam.le (sq_nonneg _)
    linarith
  -- A bound on the `y = 0` plane.
  have hzero_ge : ∀ (a : ℝ) (x : EuclideanSpace ℝ (Fin k)),
      F (a, (x, (0 : EuclideanSpace ℝ (Fin l)))) ≤ C := by
    intro a x
    have h2 := (abs_le.mp (hC0 a (x, (0 : EuclideanSpace ℝ (Fin l))))).2
    have hinner : inner ℝ (A₂ (0 : EuclideanSpace ℝ (Fin l)))
        (0 : EuclideanSpace ℝ (Fin l)) = 0 := by simp
    rw [hinner, add_zero] at h2
    dsimp only at h2
    have h5 := hA₁ x
    have h6 : (0:ℝ) ≤ lam * ‖x‖ ^ 2 := mul_nonneg hlam.le (sq_nonneg _)
    linarith
  -- The scaling radius.
  set ρ : ℝ := Real.sqrt (8 * (K / 2 + 2 * C) / lam + 1) with hρdef
  have hρarg : 0 < 8 * (K / 2 + 2 * C) / lam + 1 := by positivity
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr hρarg
  have hρineq : K / 2 + 2 * C < lam * ρ ^ 2 / 8 := by
    rw [hρdef, Real.sq_sqrt hρarg.le]
    have h : lam * (8 * (K / 2 + 2 * C) / lam + 1) = 8 * (K / 2 + 2 * C) + lam := by
      field_simp
    have h2 : lam * (8 * (K / 2 + 2 * C) / lam + 1) / 8 = (K / 2 + 2 * C) + lam / 8 := by
      rw [h]; ring
    rw [h2]; linarith
  let a₀ : ℝ := 0
  let γ₀ : EuclideanSpace ℝ (Fin k) →
      (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) := fun u => (a₀, (ρ • u, 0))
  have hγ₀cont : Continuous γ₀ := by fun_prop
  let cls : Set (EuclideanSpace ℝ (Fin k) →
      (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)))) :=
    {γ | Continuous γ ∧ ∀ u, ‖u‖ = 1 → γ u = γ₀ u}
  let A : Set ℝ := {t | ∃ γ ∈ cls, ∀ u, ‖u‖ ≤ 1 → F (γ u) ≤ t}
  have hCmem : C ∈ A := by
    refine ⟨γ₀, ⟨hγ₀cont, fun u _ => rfl⟩, fun u _ => ?_⟩
    change F (a₀, (ρ • u, (0 : EuclideanSpace ℝ (Fin l)))) ≤ C
    exact hzero_ge a₀ (ρ • u)
  have hA_ne : A.Nonempty := ⟨C, hCmem⟩
  have hA_lb : ∀ t ∈ A, -C ≤ t := by
    rintro t ⟨γ, ⟨hγc, hγb⟩, hFt⟩
    obtain ⟨u, hu1, hu0⟩ := saddle_linking_point a₀ ρ hρpos γ hγc hγb
    have hform : γ u = ((γ u).1, ((0 : EuclideanSpace ℝ (Fin k)), (γ u).2.2)) :=
      Prod.ext rfl (Prod.ext hu0 rfl)
    have h1 : -C ≤ F (γ u) := by rw [hform]; exact hzero_le (γ u).1 (γ u).2.2
    exact le_trans h1 (hFt u hu1)
  have hA_bdd : BddBelow A := ⟨-C, fun t ht => hA_lb t ht⟩
  let c : ℝ := sInf A
  have hc_lb : -C ≤ c := le_csInf hA_ne hA_lb
  have hc_ub : c ≤ C := csInf_le hA_bdd hCmem
  obtain ⟨t, htA, htc⟩ := exists_lt_of_csInf_lt hA_ne
    (show sInf A < sInf A + 1 / 2 from lt_add_of_pos_right _ (by norm_num))
  obtain ⟨γ, hγcls, hFt⟩ := htA
  obtain ⟨hγc, hγb⟩ := hγcls
  have hγF : ∀ u, ‖u‖ ≤ 1 → F (γ u) ≤ c + 1 / 2 :=
    fun u hu => (lt_of_le_of_lt (hFt u hu) (by simpa only [c] using htc)).le
  -- A bound for the image of `γ` on the closed unit ball.
  obtain ⟨Rγ, hRγ⟩ : ∃ Rγ : ℝ, ∀ u, ‖u‖ ≤ 1 → ‖γ u‖ ≤ Rγ := by
    obtain ⟨u₀, _, hu₀⟩ := (ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1).exists_isMaxOn
      ⟨0, by simp [Metric.mem_closedBall]⟩ (hγc.norm.continuousOn)
    exact ⟨‖γ u₀‖, fun u hu => (isMaxOn_iff.mp hu₀) u (by rw [Metric.mem_closedBall, dist_zero_right]; exact hu)⟩
  -- Final contradiction from a deformation `η`.
  have hfinal : ∀ (U : Set (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))))
      (c' R : ℝ), IsOpen U → (∀ z ∈ U, ‖z‖ ≤ R) → c' < c → (∀ z ∈ U, F z ≤ c') →
      (∀ u, ‖u‖ ≤ 1 → ‖γ u‖ ≤ R) → (∀ u, ‖u‖ = 1 → γ u ∈ U) → False := by
    intro U c' R hUopen hUR hc'c hU hγR hfix
    obtain ⟨η, hηcont, hηfix, hηdec⟩ := exists_descent_isotopy F hF δ hδpos hδF U hUopen R hUR
      c c' hc'c hU
    have hcont' : Continuous (η ∘ γ) := hηcont.comp hγc
    have hbnd' : ∀ u, ‖u‖ = 1 → (η ∘ γ) u = γ₀ u := by
      intro u hu
      show η (γ u) = γ₀ u
      rw [hηfix (γ u) (hfix u hu), hγb u hu]
    have hcls' : (η ∘ γ) ∈ cls := ⟨hcont', hbnd'⟩
    obtain ⟨u₁, hu₁mem, hu₁max⟩ := (ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) 1).exists_isMaxOn
      ⟨0, by simp [Metric.mem_closedBall]⟩ ((hF.continuous.comp hcont').continuousOn)
    have hsA : F ((η ∘ γ) u₁) ∈ A :=
      ⟨η ∘ γ, hcls', fun u hu => (isMaxOn_iff.mp hu₁max) u
        (by rw [Metric.mem_closedBall, dist_zero_right]; exact hu)⟩
    have hu₁ : ‖u₁‖ ≤ 1 := by rw [Metric.mem_closedBall, dist_zero_right] at hu₁mem; exact hu₁mem
    have hsc : F ((η ∘ γ) u₁) < c := by
      have hdec := hηdec (γ u₁) (hγR u₁ hu₁) (hγF u₁ hu₁)
      have h1 : F (γ u₁) - 1 < c := by linarith [hγF u₁ hu₁]
      have h2 : (c + c') / 2 < c := by linarith
      calc F ((η ∘ γ) u₁) = F (η (γ u₁)) := rfl
        _ ≤ max (F (γ u₁) - 1) ((c + c') / 2) := hdec
        _ < c := max_lt h1 h2
    have := csInf_le hA_bdd hsA
    linarith
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: no boundary condition, `U = ∅`.
    refine hfinal ∅ (c - 1) Rγ isOpen_empty (fun z hz => by simp at hz) (by linarith)
      (fun z hz => by simp at hz) (fun u hu => hRγ u hu)
      (fun u hu => absurd hu (by
        haveI : Subsingleton (EuclideanSpace ℝ (Fin k)) := by rw [hk0]; infer_instance
        rw [Subsingleton.elim u 0]; simp))
  · -- `k ≥ 1`: the boundary sphere lies in a neighbourhood `U` on which `F ≤ c'`.
    set c' : ℝ := -lam * ρ ^ 2 / 8 + K / 2 + C with hc'def
    let U : Set (ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))) :=
      {z | |z.1 - a₀| < 1} ∩ {z | ρ / 2 < ‖z.2.1‖} ∩ {z | ‖z.2.1‖ < 2 * ρ} ∩
        {z | ‖z.2.2‖ < 1}
    have hc'c : c' < c := by
      have h1 : c' < -C := by rw [hc'def]; linarith [hρineq]
      linarith
    have hUopen : IsOpen U := by
      have h1 : IsOpen {z : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) |
          |z.1 - a₀| < 1} :=
        isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const)) continuous_const
      have h2 : IsOpen {z : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) |
          ρ / 2 < ‖z.2.1‖} := isOpen_lt continuous_const (continuous_snd.fst.norm)
      have h3 : IsOpen {z : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) |
          ‖z.2.1‖ < 2 * ρ} := isOpen_lt (continuous_snd.fst.norm) continuous_const
      have h4 : IsOpen {z : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l)) |
          ‖z.2.2‖ < 1} := isOpen_lt (continuous_snd.snd.norm) continuous_const
      exact ((h1.inter h2).inter h3).inter h4
    have hUbound : ∀ z ∈ U, F z ≤ c' := by
      intro z hz
      simp only [U, Set.mem_inter_iff, Set.mem_setOf_eq] at hz
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hz
      have hA1z := hA₁ z.2.1
      have hA2z : inner ℝ (A₂ z.2.2) z.2.2 ≤ K * ‖z.2.2‖ ^ 2 :=
        calc inner ℝ (A₂ z.2.2) z.2.2 ≤ ‖A₂ z.2.2‖ * ‖z.2.2‖ := real_inner_le_norm _ _
          _ ≤ (K * ‖z.2.2‖) * ‖z.2.2‖ := by
              gcongr
              exact hA₂' z.2.2
          _ = K * ‖z.2.2‖ ^ 2 := by ring
      have hhalf := (abs_le.mp (hC0 z.1 (z.2.1, z.2.2))).2
      have hnorm1 : lam * ‖z.2.1‖ ^ 2 / 2 > lam * ρ ^ 2 / 8 := by
        have h : ρ / 2 < ‖z.2.1‖ := h2
        have hsq : (ρ / 2) ^ 2 < ‖z.2.1‖ ^ 2 := by
          nlinarith [h, hρpos, norm_nonneg z.2.1]
        have h2' : lam * (ρ / 2) ^ 2 / 2 < lam * ‖z.2.1‖ ^ 2 / 2 := by
          have := mul_lt_mul_of_pos_left hsq hlam
          linarith [this]
        have heq : lam * (ρ / 2) ^ 2 / 2 = lam * ρ ^ 2 / 8 := by ring
        linarith [h2', heq]
      have hnorm2 : K * ‖z.2.2‖ ^ 2 / 2 ≤ K / 2 := by
        have h : ‖z.2.2‖ < 1 := h4
        have hsq : ‖z.2.2‖ ^ 2 < 1 := by nlinarith [h, norm_nonneg z.2.2]
        nlinarith [hsq, hK]
      show F (z.1, (z.2.1, z.2.2)) ≤ c'
      rw [hc'def]
      linarith [hhalf, hA1z, hA2z, hnorm1, hnorm2]
    have hUbdd : ∀ z ∈ U, ‖z‖ ≤ max (|a₀| + 1) (max (2 * ρ) 1) := by
      intro z hz
      simp only [U, Set.mem_inter_iff, Set.mem_setOf_eq] at hz
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hz
      have hz1 : |z.1| ≤ |a₀| + 1 := by
        have h : |z.1 - a₀| < 1 := h1
        calc |z.1| = |(z.1 - a₀) + a₀| := by rw [sub_add_cancel]
          _ ≤ |z.1 - a₀| + |a₀| := abs_add_le _ _
          _ ≤ 1 + |a₀| := by linarith
          _ = |a₀| + 1 := by ring
      rw [Prod.norm_mk, Prod.norm_mk]
      refine max_le (le_trans hz1 (le_max_left _ _))
        (le_trans (max_le ?_ ?_) (le_max_right _ _))
      · exact le_trans (le_of_lt h3) (le_max_left _ _)
      · exact le_trans (le_of_lt h4) (le_max_right _ _)
    have hfix : ∀ u, ‖u‖ = 1 → γ₀ u ∈ U := by
      intro u hu
      simp only [U, Set.mem_inter_iff, Set.mem_setOf_eq]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · show |a₀ - a₀| < 1
        simp
      · show ρ / 2 < ‖ρ • u‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos, hu, mul_one]
        linarith
      · show ‖ρ • u‖ < 2 * ρ
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos, hu, mul_one]
        linarith
      · show ‖(0 : EuclideanSpace ℝ (Fin l))‖ < 1
        simp
    exact hfinal U c' (max (max (|a₀| + 1) (max (2 * ρ) 1)) Rγ) hUopen
      (fun z hz => le_trans (hUbdd z hz) (le_max_left _ _)) hc'c hUbound
      (fun u hu => le_trans (hRγ u hu) (le_max_right _ _))
      (fun u hu => by rw [hγb u hu]; exact hfix u hu)

end Work.RPCore.Saddle
