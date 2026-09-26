import Mathlib
import ChallengeDeps
import Submission.TorusChartLift

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

/-!
# Layer A (xiii) — the atlas of the trisecant zero set: honest charts, cover, overlap

The three `torus_chart_lift_*` theorems (`TorusChartLift.lean`) give, for each
of the rank-two witness pairs `(A,B)`, `(A,M)`, `(B,M)` at a collinear
off-diagonal general-position real triple, an **honest torus chart**: an open
neighbourhood `V` of the base point `torusQuotient (a,(b,m))` in `T³`, and a
single injective continuous parametrisation `γ` over an open interval whose
image is exactly `trisecantZeroSet r ∩ V`.  This module opens the
**global-atlas** stage:

1. **`ZeroSetChart r p`** — the bundled chart record
   (`V` open ∋ `p`, base parameter `x₀ ∈ (lo,hi)`, `γ` continuous injective
   on `(lo,hi)`, `γ x₀ = p`, and the chart identity
   `image_eq : γ '' (lo,hi) = trisecantZeroSet r ∩ V`);
2. **per-witness covers** `zeroSetChart_cover_AB/AM/BM` — assemble the chart
   from the corresponding `torus_chart_lift_*` (via the splitting instances
   and a small `δ` from `RealGraphArc.exists_small_delta`);
3. **the atlas / cover theorem** `zeroSetChart_at_general_position`: under
   the torus general-position hypothesis every collinear off-diagonal torus
   triple carries a `ZeroSetChart` (dispatch over the rank-two witness by
   `fin_cases`, mapped to `(A,B)`/`(A,M)`/`(B,M)` with the order-swap lemma
   `linearIndependent_pair_swap_iff`, mirroring
   `smooth_local_curve_of_general_position`);
4. **overlap compatibility** `zeroSetChart_overlap` /
   `zeroSetChart_agree_on_overlap`: two charts at the same base point `p`
   agree on `W = V₁ ∩ V₂` — both curves trace exactly
   `trisecantZeroSet r ∩ W` there.  Every later double-point claim reduces
   to this compatibility: a point covered by two charts is a single point of
   the common zero set, reached once by each (injective) parametrisation.

(The full component/1-manifold statement is the next gluing stage, built on
the cover + overlap facts below.)

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- **An honest torus chart of the trisecant zero set at `p`**: an open
torus neighbourhood `V` of `p`, a base parameter `x₀` inside the interval
`(lo,hi)`, and an injective continuous curve `γ` over `(lo,hi)` with
`γ x₀ = p` whose image is *exactly* `trisecantZeroSet r ∩ V`. -/
structure ZeroSetChart (r : ℝ → Space) (p : KnotParamTriple) where
  V : Set KnotParamTriple
  V_open : IsOpen V
  p_mem : p ∈ V
  x₀ : ℝ
  lo : ℝ
  hi : ℝ
  x₀_mem : x₀ ∈ Set.Ioo lo hi
  γ : ℝ → KnotParamTriple
  γ_cont : ContinuousOn γ (Set.Ioo lo hi)
  γ_inj : Set.InjOn γ (Set.Ioo lo hi)
  γ_base : γ x₀ = p
  image_eq : γ '' Set.Ioo lo hi = trisecantZeroSet r ∩ V

/-- A small interval half-width around the base parameter `u.1` that keeps
the graph inside `(d.a, d.b)` and has width `< period` (exists because the
parameter interval is nondegenerate and the period is positive). -/
lemma RealGraphArc.exists_small_delta {r : ℝ → Space} (d : RealGraphArc r) :
    ∃ δ : ℝ, 0 < δ ∧ 2 * δ < period ∧ d.a < d.u.1 - δ ∧ d.u.1 + δ < d.b := by
  have hP1 : 0 < d.u.1 - d.a := by linarith [d.a_lt]
  have hP2 : 0 < d.b - d.u.1 := by linarith [d.u_lt_b]
  have hper : 0 < period := period_pos
  let s : ℝ := min (d.u.1 - d.a) (min (d.b - d.u.1) (period / 2))
  have hs : 0 < s := by
    dsimp [s]
    exact lt_min hP1 (lt_min hP2 (div_pos hper (by norm_num)))
  have hs1 : s ≤ d.u.1 - d.a := by
    dsimp [s]
    exact min_le_left _ _
  have hs2 : s ≤ d.b - d.u.1 := by
    dsimp [s]
    exact le_trans (min_le_right (d.u.1 - d.a) (min (d.b - d.u.1) (period / 2)))
      (min_le_left (d.b - d.u.1) (period / 2))
  have hs3 : s ≤ period / 2 := by
    dsimp [s]
    exact le_trans (min_le_right (d.u.1 - d.a) (min (d.b - d.u.1) (period / 2)))
      (min_le_right (d.b - d.u.1) (period / 2))
  let δ : ℝ := s / 2
  refine ⟨δ, ?_, ?_, ?_, ?_⟩
  · dsimp [δ]
    exact div_pos hs (by norm_num)
  · dsimp [δ]
    have h2 : 2 * (s / 2) = s := by ring
    nlinarith [h2, hs3, hper]
  · dsimp [δ]
    have h1 : s < 2 * (d.u.1 - d.a) := by nlinarith [hs1, hP1]
    nlinarith
  · dsimp [δ]
    have h2 : s < 2 * (d.b - d.u.1) := by nlinarith [hs2, hP2]
    nlinarith

/-- Assemble a `ZeroSetChart` from a `torus_chart_lift_*` output (the image
equality is the two inclusions: the curve stays in the zero set and in `V`,
and the covering puts every zero of `V` on the curve). -/
def zeroSetChart_of_lift {r : ℝ → Space} {p : KnotParamTriple} {x₀ lo hi : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo lo hi) {V : Set KnotParamTriple} (hVo : IsOpen V)
    (hVp : p ∈ V) {γ : ℝ → KnotParamTriple} (hγc : ContinuousOn γ (Set.Ioo lo hi))
    (hγi : Set.InjOn γ (Set.Ioo lo hi)) (hγb : γ x₀ = p)
    (hγZ : γ '' Set.Ioo lo hi ⊆ trisecantZeroSet r)
    (hγV : γ '' Set.Ioo lo hi ⊆ V)
    (hcover : ∀ q ∈ V, q ∈ trisecantZeroSet r → ∃ x ∈ Set.Ioo lo hi, γ x = q) :
    ZeroSetChart r p := by
  have himg : γ '' Set.Ioo lo hi = trisecantZeroSet r ∩ V := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hγZ ⟨x, hx, rfl⟩, hγV ⟨x, hx, rfl⟩⟩
    · intro hq
      rcases hq with ⟨hqz, hqv⟩
      rcases hcover q hqv hqz with ⟨x, hx, hxq⟩
      exact ⟨x, hx, hxq⟩
  exact ⟨V, hVo, hVp, x₀, lo, hi, hx₀, γ, hγc, hγi, hγb, himg⟩

/-- **Cover, `(A,B)` witness**: a collinear off-diagonal triple with
independent `a`/`b` partials has an honest torus chart at
`torusQuotient (a,(b,m))`. -/
theorem zeroSetChart_cover_AB {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialB r a b m]) :
    Nonempty (ZeroSetChart r (torusQuotient (a, (b, m)))) := by
  rcases exists_realGraphArc_AB_splitting h a b m hΦ hZ hW0 hmb hLI with ⟨d, hB, hA, hu⟩
  rcases d.exists_small_delta with ⟨δ, hδpos, hδw, hL, hR⟩
  have hLm : d.a < m - δ := by
    rw [hu] at hL
    exact hL
  have hRm : m + δ < d.b := by
    rw [hu] at hR
    exact hR
  rcases torus_chart_lift_AB h a b m hδpos hδw d hB hA hu hLm hRm with
    ⟨V, hVo, hVp, γ, hγc, hγi, hγb, hsub, hVset, hcover⟩
  exact ⟨zeroSetChart_of_lift (r := r) (p := torusQuotient (a, (b, m)))
    (x₀ := m) (lo := m - δ) (hi := m + δ) (by constructor <;> linarith)
    hVo hVp hγc hγi hγb hsub hVset hcover⟩

/-- **Cover, `(A,M)` witness**: as `zeroSetChart_cover_AB` for independent
`a`/`m` partials. -/
theorem zeroSetChart_cover_AM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialA r a b m, collPartialM r a b m]) :
    Nonempty (ZeroSetChart r (torusQuotient (a, (b, m)))) := by
  rcases exists_realGraphArc_AM_splitting h a b m hΦ hZ hW0 hmb hLI with ⟨d, hB, hA, hu⟩
  rcases d.exists_small_delta with ⟨δ, hδpos, hδw, hL, hR⟩
  have hLb : d.a < b - δ := by
    rw [hu] at hL
    exact hL
  have hRb : b + δ < d.b := by
    rw [hu] at hR
    exact hR
  rcases torus_chart_lift_AM h a b m hδpos hδw d hB hA hu hLb hRb with
    ⟨V, hVo, hVp, γ, hγc, hγi, hγb, hsub, hVset, hcover⟩
  exact ⟨zeroSetChart_of_lift (r := r) (p := torusQuotient (a, (b, m)))
    (x₀ := b) (lo := b - δ) (hi := b + δ) (by constructor <;> linarith)
    hVo hVp hγc hγi hγb hsub hVset hcover⟩

/-- **Cover, `(B,M)` witness**: as `zeroSetChart_cover_AB` for independent
`b`/`m` partials. -/
theorem zeroSetChart_cover_BM {r : ℝ → Space} (h : IsSmoothKnot r) (a b m : ℝ)
    (hΦ : collinearityValue r a b m = 0)
    (hZ : r a - r b ≠ 0) (hW0 : r a - r m ≠ 0) (hmb : r m - r b ≠ 0)
    (hLI : LinearIndependent ℝ ![collPartialB r a b m, collPartialM r a b m]) :
    Nonempty (ZeroSetChart r (torusQuotient (a, (b, m)))) := by
  rcases exists_realGraphArc_BM_splitting h a b m hΦ hZ hW0 hmb hLI with ⟨d, hB, hA, hu⟩
  rcases d.exists_small_delta with ⟨δ, hδpos, hδw, hL, hR⟩
  have hLa : d.a < a - δ := by
    rw [hu] at hL
    exact hL
  have hRa : a + δ < d.b := by
    rw [hu] at hR
    exact hR
  rcases torus_chart_lift_BM h a b m hδpos hδw d hB hA hu hLa hRa with
    ⟨V, hVo, hVp, γ, hγc, hγi, hγb, hsub, hVset, hcover⟩
  exact ⟨zeroSetChart_of_lift (r := r) (p := torusQuotient (a, (b, m)))
    (x₀ := a) (lo := a - δ) (hi := a + δ) (by constructor <;> linarith)
    hVo hVp hγc hγi hγb hsub hVset hcover⟩

/-- **The atlas / cover theorem**: under the torus general-position
hypothesis, every collinear off-diagonal torus triple carries an honest
`ZeroSetChart`.  (Dispatch over the rank-two witness pair: each unordered
pair of hinge partials is one of `(A,B)`, `(A,M)`, `(B,M)`, with the
order-swap lemma handling the reversed orderings.) -/
theorem zeroSetChart_at_general_position {r : ℝ → Space} (h : IsSmoothKnot r)
    (hgp : TorusGeneralPosition r) (p : KnotParamTriple)
    (hp : p ∈ trisecantZeroSet r) : Nonempty (ZeroSetChart r p) := by
  have hpZ : torusCollinearity r p = 0 := (mem_trisecantZeroSet_iff p).mp hp |>.1
  have hpOff : p ∈ TorusOffDiag r := (mem_trisecantZeroSet_iff p).mp hp |>.2
  rcases hgp p hpZ hpOff with ⟨a, b, m, ha, hb, hm, hpa, hpb, hpm, hGP⟩
  rcases hGP with ⟨hZa, hW0, hmb, hP⟩
  rcases hP with ⟨i, j, hij, hLIij⟩
  have hp_eq : torusQuotient (a, (b, m)) = p := by
    simp [torusQuotient, hpa, hpb, hpm]
  have hΦ : collinearityValue r a b m = 0 := by
    rw [← hp_eq] at hpZ
    rw [torusCollinearity_quotient h (a, (b, m))] at hpZ
    simpa [collinearityValue_eq, collinearityMap] using hpZ
  rw [← hp_eq]
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact zeroSetChart_cover_AB h a b m hΦ hZa hW0 hmb
      (by simpa [collPartial_eq_A, collPartial_eq_B] using hLIij)
  · exact zeroSetChart_cover_AM h a b m hΦ hZa hW0 hmb
      (by simpa [collPartial_eq_A, collPartial_eq_M] using hLIij)
  · exact zeroSetChart_cover_AB h a b m hΦ hZa hW0 hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialA r a b m) (collPartialB r a b m)).mp ?_
        · simpa [collPartial_eq_A, collPartial_eq_B] using hsw
        · simpa [collPartial_eq_A, collPartial_eq_B] using hLIij)
  · exact False.elim (hij rfl)
  · exact zeroSetChart_cover_BM h a b m hΦ hZa hW0 hmb
      (by simpa [collPartial_eq_B, collPartial_eq_M] using hLIij)
  · exact zeroSetChart_cover_AM h a b m hΦ hZa hW0 hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialA r a b m) (collPartialM r a b m)).mp ?_
        · simpa [collPartial_eq_A, collPartial_eq_M] using hsw
        · simpa [collPartial_eq_A, collPartial_eq_M] using hLIij)
  · exact zeroSetChart_cover_BM h a b m hΦ hZa hW0 hmb
      (by
        have hsw := (linearIndependent_pair_swap_iff (collPartialB r a b m) (collPartialM r a b m)).mp ?_
        · simpa [collPartial_eq_B, collPartial_eq_M] using hsw
        · simpa [collPartial_eq_B, collPartial_eq_M] using hLIij)
  · exact False.elim (hij rfl)

/-- **Overlap compatibility**: two charts at the same base point `p` agree
on `W = V₁ ∩ V₂`: each curve traces exactly `trisecantZeroSet r ∩ W` there.
(Every double-point claim reduces to this: a point covered by both charts
is a single point of the common zero set.) -/
theorem zeroSetChart_overlap {r : ℝ → Space} {p : KnotParamTriple}
    (c₁ c₂ : ZeroSetChart r p) :
    (c₁.γ '' Set.Ioo c₁.lo c₁.hi) ∩ (c₁.V ∩ c₂.V) = trisecantZeroSet r ∩ (c₁.V ∩ c₂.V) ∧
    (c₂.γ '' Set.Ioo c₂.lo c₂.hi) ∩ (c₁.V ∩ c₂.V) = trisecantZeroSet r ∩ (c₁.V ∩ c₂.V) ∧
    IsOpen (c₁.V ∩ c₂.V) ∧ p ∈ c₁.V ∩ c₂.V := by
  constructor
  · rw [c₁.image_eq]
    ext q
    simp only [Set.mem_inter_iff]
    tauto
  constructor
  · rw [c₂.image_eq]
    ext q
    simp only [Set.mem_inter_iff]
    tauto
  constructor
  · exact c₁.V_open.inter c₂.V_open
  · exact ⟨c₁.p_mem, c₂.p_mem⟩

/-- The two curves of charts at the same point trace the same portion of the
zero set on the overlap (germ-level agreement used for gluing). -/
theorem zeroSetChart_agree_on_overlap {r : ℝ → Space} {p : KnotParamTriple}
    (c₁ c₂ : ZeroSetChart r p) :
    (c₁.γ '' Set.Ioo c₁.lo c₁.hi) ∩ (c₁.V ∩ c₂.V) =
      (c₂.γ '' Set.Ioo c₂.lo c₂.hi) ∩ (c₁.V ∩ c₂.V) := by
  rw [c₁.image_eq, c₂.image_eq]
  ext q
  simp only [Set.mem_inter_iff]
  tauto

end LeanEval.KnotTheory.Quadrisecant
