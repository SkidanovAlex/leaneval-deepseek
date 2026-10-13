/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/SmoothOpenIterProd.lean` — the `SmoothOpen` clause of `hkeepIter`,
# produced from the engine's prefix induction + the lead's Fubini ruling

The lead's ruling on finding (XXIII) (`sources/ftsV2/fts_e4_smoothopen_ruling.md`; installed as
`EpsEngine/SmoothOpenIter.lean`) shows that one Picard step preserves `SmoothOpen`
(`SORuling.smoothOpen_iter_succ_XBall`), from the following three inputs about the level-`n` curve:

* `hP`   — the class data of the levels `≤ n` (the *prefix* form!),
* `hEq`  — the time-Lipschitz bound `EpsSq (w_s − w_t) ≤ L (s−t)²` (the Minkowski step),
* `hFint` — pointwise interval integrability of the integrand.

This module *produces* `hEq` and `hFint` from the engine's prefix induction
(`IterContMeas.iter_cont_meas_prefix` and `EpsSq_iter_succ_sub_le`), so that the consumer only has
to supply the class data of the levels `≤ n` and the two gates of `Feps` on `XBall`.  The result is
the exact form in which `hkeepIter` is proved by induction:

    theorem smoothOpen_iter_succ_XBall_prefix … (hP : ∀ m ≤ n, … XBall … (iterate m)) :
      ∀ τ ∈ Icc 0 δ, SmoothOpen (slice (iterate (n+1)) τ).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.IterContMeas
import Submission.Work.FTS.EpsEngine.SmoothOpenIter

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The time-Lipschitz bound of the `(n+1)`-st Picard curve** (the `hEq` input of the lead's
Fubini lemma, in the ordered form): the increment of the `(n+1)`-st iterate over `(a,b] ⊆ [0,δ]` is
the parametric integral of the level-`n` curve, so the Minkowski bound gives
`EpsSq (w_a − w_b) ≤ (b−a)²·L`. -/
theorem EpsSq_iter_succ_sub_le {α L δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} (n : ℕ)
    (hL : 0 ≤ L)
    (hPn : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (slice (iter F h₀ n) p.1) p.2.1 p.2.2)
      (((volume : Measure ℝ).restrict (Set.Icc 0 δ)).prod volume))
    (hcont_n : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s : ℝ => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ)) :
    ∀ a ∈ Set.Icc 0 δ, ∀ b ∈ Set.Icc 0 δ, a ≤ b →
      EpsSq α (fun z θ => slice (iter F h₀ (n + 1)) a z θ
        - slice (iter F h₀ (n + 1)) b z θ) ≤ (b - a) * ((b - a) * L) := by
  intro a ha b hb hab
  have hbound := EpsSq_integral_iter_le (α := α) (L := L) (δ := δ) (F := F) (h₀ := h₀) (P := P)
    n hL hPn hbd haesm
  have hiter : ∀ τ z' θ' : ℝ, slice (iter F h₀ (n + 1)) τ z' θ'
      = h₀ z' θ' + ∫ t in (0 : ℝ)..τ, F (slice (iter F h₀ n) t) z' θ' := by
    intro τ z' θ'
    rw [iter_succ F h₀ n]
    simp only [Work.FTS.Galerkin.slice_apply]
  have hdiff : ∀ᵐ p ∂DomM,
      (fun z' θ' => slice (iter F h₀ (n + 1)) a z' θ'
        - slice (iter F h₀ (n + 1)) b z' θ') p.1 p.2
        = (fun z' θ' => -∫ t in a..b, F (slice (iter F h₀ n) t) z' θ') p.1 p.2 := by
    filter_upwards [ae_open_DomM] with p hp
    obtain ⟨hz', hθ'0, hθ'1⟩ := hp
    have hc : ContinuousOn (fun t : ℝ => F (slice (iter F h₀ n) t) p.1 p.2)
        (Set.Icc 0 δ) := hcont_n p.1 p.2 hz' hθ'0 hθ'1
    rw [hiter a p.1 p.2, hiter b p.1 p.2]
    have h1 : IntervalIntegrable (fun t : ℝ => F (slice (iter F h₀ n) t) p.1 p.2) volume 0 a :=
      ContinuousOn.intervalIntegrable_of_Icc ha.1 (hc.mono (Set.Icc_subset_Icc_right ha.2))
    have h2 : IntervalIntegrable (fun t : ℝ => F (slice (iter F h₀ n) t) p.1 p.2) volume a b :=
      ContinuousOn.intervalIntegrable_of_Icc hab
        (hc.mono (fun x hx => ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩))
    have hadj := (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    rw [hadj]
    ring
  have h0 := EpsSq_congr_ae (α := α)
    (f := fun z' θ' => slice (iter F h₀ (n + 1)) a z' θ'
      - slice (iter F h₀ (n + 1)) b z' θ')
    (g := fun z' θ' => -∫ t in a..b, F (slice (iter F h₀ n) t) z' θ') hdiff
  rw [h0, EpsSq_neg2]
  exact hbound a ha b hb hab

/-- **The time-Lipschitz bound `hEq`** in the shape consumed by the lead's
`SORuling.smoothOpen_iter_succ_XBall` (`Lw = L`): `EpsSq (w_s − w_t) ≤ L (s−t)²` for all
`s, t ∈ [0,δ]`. -/
theorem EpsSq_iter_sub_sq_le {α Cpt L δ : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} (n : ℕ)
    (hδ : 0 < δ) (hL : 0 ≤ L) (hCpt : 0 ≤ Cpt)
    (hP : ∀ m : ℕ, m ≤ n → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ m) τ))
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → F u q.1 q.2 = 0)
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (hpt : ∀ u v : Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ))) :
    ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, EpsSq α (fun z θ =>
      slice (iter F h₀ n) s z θ - slice (iter F h₀ n) t z θ) ≤ L * (s - t) ^ 2 := by
  intro s hs t ht
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- level `0`: the curve is constant (the iterate `0` is `h₀`)
    subst hn
    have hz : (fun z θ => slice (iter F h₀ 0) s z θ - slice (iter F h₀ 0) t z θ)
        = fun _ _ => (0 : ℝ) := by
      funext z θ
      simp only [iter_zero, Work.FTS.Galerkin.slice_apply, sub_self]
    rw [hz, EpsSq_zero]
    exact mul_nonneg hL (sq_nonneg _)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hcont_meas := iter_cont_meas_prefix (α := α) (Cpt := Cpt) (L := L) (δ := δ)
      (F := F) (h₀ := h₀) (P := P) k hδ hL hCpt (fun m hm => hP m (by omega))
      hcontP hzeroP hbd hpt
    obtain ⟨hcontAll, haesmAll⟩ := hcont_meas
    rcases le_total s t with hle | hle
    · refine le_trans (EpsSq_iter_succ_sub_le (α := α) (L := L) (δ := δ) (F := F) (h₀ := h₀)
        (P := P) k hL (hP k (by omega)) hbd (haesmAll k (by omega))
        (hcontAll k (by omega)) s hs t ht hle) (le_of_eq ?_)
      rw [show (t - s) * ((t - s) * L) = L * (s - t) ^ 2 by ring]
    · have h := EpsSq_iter_succ_sub_le (α := α) (L := L) (δ := δ) (F := F) (h₀ := h₀)
        (P := P) k hL (hP k (by omega)) hbd (haesmAll k (by omega))
        (hcontAll k (by omega)) t ht s hs hle
      have heq : (fun z θ => slice (iter F h₀ (k + 1)) s z θ
          - slice (iter F h₀ (k + 1)) t z θ)
          = fun z θ => -(slice (iter F h₀ (k + 1)) t z θ
            - slice (iter F h₀ (k + 1)) s z θ) := by
        funext z θ; ring
      rw [heq, EpsSq_neg2]
      refine le_trans h (le_of_eq ?_)
      rw [show (s - t) * ((s - t) * L) = L * (s - t) ^ 2 by ring]

/-- **The `SmoothOpen` clause of `hkeepIter`, in the prefix form needed by its induction**: if the
levels `≤ n` of the Picard iteration of `Feps` all lie in `XBall` on `[0,δ]` (and the two gates of
`Feps` hold on `XBall`), then every slice of the `(n+1)`-st iterate is `SmoothOpen`.  This is the
lead's `SORuling.smoothOpen_iter_succ_XBall` with its two remaining inputs produced by
`iter_cont_meas_prefix` (`hFint`) and `EpsSq_iter_sub_sq_le` (`hEq`, with `Lw = L`). -/
theorem smoothOpen_iter_succ_XBall_prefix {α C₀ R Ce Cs Cpt L δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {ε : ℝ} {h₀ : Fn} (n : ℕ)
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E) (hR : 0 ≤ R)
    (hδ : 0 < δ) (hL : 0 ≤ L) (hCpt : 0 ≤ Cpt)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hP : ∀ m : ℕ, m ≤ n → ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → XBall α ρ ε R C₀
      (slice (iter (Feps α ρ ε Φs E) h₀ m) τ))
    (hcontP : ∀ u : Fn, XBall α ρ ε R C₀ u → ContinuousOn (fun q : ℝ × ℝ =>
      Feps α ρ ε Φs E u q.1 q.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzeroP : ∀ u : Fn, XBall α ρ ε R C₀ u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E u q.1 q.2 = 0)
    (hbd : ∀ u : Fn, XBall α ρ ε R C₀ u →
      EpsMem α (Feps α ρ ε Φs E u) ∧ EpsSq α (Feps α ρ ε Φs E u) ≤ L)
    (hpt : ∀ u v : Fn, XBall α ρ ε R C₀ u → XBall α ρ ε R C₀ v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ))) :
    ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      Work.FTS.EllipticEst.SmoothOpen (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) := by
  obtain ⟨hcontAll, _haesmAll⟩ :=
    iter_cont_meas_prefix (α := α) (Cpt := Cpt) (L := L) (δ := δ)
      (F := Feps α ρ ε Φs E) (h₀ := h₀) (P := fun u => XBall α ρ ε R C₀ u)
      n hδ hL hCpt hP hcontP hzeroP hbd hpt
  have hEq := EpsSq_iter_sub_sq_le (α := α) (Cpt := Cpt) (L := L) (δ := δ)
    (F := Feps α ρ ε Φs E) (h₀ := h₀) (P := fun u => XBall α ρ ε R C₀ u)
    n hδ hL hCpt hP hcontP hzeroP hbd hpt
  have hFint : ∀ τ ∈ Set.Icc 0 δ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      IntervalIntegrable (fun s => Feps α ρ ε Φs E
        (slice (iter (Feps α ρ ε Φs E) h₀ n) s) z θ) volume 0 τ := by
    intro τ hτ z θ hz hθ
    exact ContinuousOn.intervalIntegrable_of_Icc hτ.1
      (((hcontAll n le_rfl) z θ hz hθ.1 hθ.2).mono (Set.Icc_subset_Icc_right hτ.2))
  intro τ hτ
  exact SORuling.smoothOpen_iter_succ_XBall (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := L) (δ := δ) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀)
    hα hρ hε hε1 hEll hstar hml hR hL n h0 (fun s hs => hP n le_rfl s hs) hEq hFint hτ

end Work.FTS.EpsEngine
