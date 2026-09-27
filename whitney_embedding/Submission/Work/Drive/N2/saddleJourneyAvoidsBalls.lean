import Mathlib
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.modelOrbitInvariant

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

/-!
# The legality of the saddle-window transport (re-posed: `0 < R` added)

This is the statement held in `Submission/Work/Drive/N2/windowLegality_holder.lean` (modulo
qualification) with **two** repairs, both forced by counterexamples found by earlier provers:

1. `(hfcont : Continuous f)` — without it the held statement is FALSE, see
   `Submission/Work/Drive/N2/NOTES_windowJourneyAvoidsBalls_FALSE.md` (a journey can enter a *foreign*
   chart's model ball because `hsep` constrains `f` only on the open balls while `hlevel` only speaks
   about ball-free segments).  Free in the application (`f` is C^∞);
2. `(hRpos : 0 < R)` — without it the statement is FALSE even with `Continuous f`, see
   `Submission/Work/Drive/N2/NOTES_saddleJourneyAvoidsBalls_COUNTEREXAMPLE.md`
   (`hR : η² + (r j)⁴ < R⁴` carries no information for `R < 0`, and the entry bound `ρ⁴ − η² > (r j)⁴`
   at the exit point of the chart source fails).  `R` is a *radius* in the intended use, so
   `0 < R` is free there.

With these two, the classical prefix argument goes through; here it is in full.

Put `T := c - η - f x₀ < 0`, `I := Icc T 0`, `Ball i := Work.Drive.N2.modelBall (φ i) (r i)`, and
`G := {u | u ∈ I ∧ ∀ w ∈ Icc u 0, ∀ i, Φ (w, x₀) ∉ Ball i}`.  Note `0 < R` + `hR` + `hρR` give
`(r j)² < R < ρ` and hence `(r j)⁴ < η² + (r j)⁴ < R⁴ < ρ⁴`.

**(0)** `x₀ ∉ Ball i` for every `i`: for `i ≠ j` this is `hsep` + `hwin`; for `i = j`, if `x₀ ∈ Ball j`
then `x₀ ∈ (φ j).source`, `hvalj` gives `|Re (Z x₀)²| = |f x₀ - c| < η`, and `hD` + `hwin` + `hvalj`
force `c₀ ≤ |Im (Z x₀)²|`, so `‖Z x₀‖⁴ > c₀² > (r j)⁴`, contradicting `‖Z x₀‖ = ‖φ j x₀‖ < r j`.

**(1)** `0 ∈ G` by (0) and `hΦ0`; on `G` the conditional level law `hlevel` applied at `x₀` (its
hypothesis is *exactly* the avoidance on `Icc (min 0 w) (max 0 w) = Icc w 0`) gives
`f (Φ (w,x₀)) = f x₀ + w`, whence `f (Φ (w,x₀)) ∈ Icc (c - η) (c + η)` for `w ∈ Icc u 0`.

**(2)** `G` is closed.  For `u ∉ G`: if `u ∉ Icc T 0` use that `Icc T 0` is closed; otherwise there
are `w ∈ Icc u 0` and `i` with `Φ (w,x₀) ∈ Ball i`, which is *open*.  If `u < w`, then
`w ∈ Icc u' 0` for all `u' ∈ Ioo (2u - w) w`.  If `w = u`, then by `horbit` and openness of `Ball i`,
all `u'` near `u` have `Φ (u',x₀) ∈ Ball i`, and `u' ∈ Icc u' 0` (when `u' ≤ 0`), so again `u' ∉ G`.

**(3)** The openness step: for `u ∈ G` with `T < u` there is `δ > 0` with `u - δ ∈ G`.
 * `|f (Φ (u,x₀)) - c| < η`: the value is `f x₀ + u` by (1), and `u ∈ (T, 0]`.
 * `u ↦ f (Φ (u,x₀))` is continuous at `u` (`hfcont` + `horbit`); choose `δ` (half the continuity
   modulus) so that `|w - u| ≤ δ ⟹ |f (Φ (w,x₀)) - c| < η`: the values on `Icc (u-δ) 0` are in the
   *closed* window (`[f x₀ + u, f x₀]` by the level law for `w ≥ u`, and the continuity choice below).
 * For `w ∈ Icc (u-δ) 0` show `∀ i, Φ (w,x₀) ∉ Ball i`:
   - `i ≠ j`: `hsep` would give `η < |f (Φ (w,x₀)) - c|`;
   - `i = j`: `notMem_modelBall_home` (below), whose proof is the maximal-source argument: let
     `A := {v | ∀ u' ∈ Icc w v, Φ (u',x₀) ∈ (φ j).source}` (nonempty: `z ∈ (φ j).source` because
     `Ball j ⊆ (φ j).source`) and `β := sSup (A ∩ Icc w 0)` (bounded above by `0`).  Then
     `[w,β) ⊆ (φ j).source`; if the orbit is in the source at `β`, openness of the source and
     `β = sSup` force `β = 0`, and then `x₀` is in the source, so `hD` + `hwin` + `hvalj` give the
     invariant `c₀ ≤ |Im (Z x₀)²|`, conserved down to `w`.  Otherwise `‖Z (Φ (β,x₀))‖ = ρ` (limit
     from below + off-source), the value at `β` lies in the closed window (either by (1) for
     `β ≥ u`, or by the continuity choice for `u - δ ≤ β < u`), so `|Re (Z (Φ (β,x₀)))²| ≤ η` and
     `|Im|² ≥ ρ⁴ - η² > (r j)⁴`; conservation along `[w,u']` for `u' < β` plus the limit `u' ↑ β`
     transfers this to `z := Φ (w,x₀)`.  In every case `‖Z z‖⁴ ≥ |Im (Z z)²|² > (r j)⁴`, so
     `‖φ j z‖ = ‖Z z‖ > r j`, contradicting `z ∈ Ball j`.
 * Combine: the avoidance on `Icc (u-δ) 0` just proved (with `w := u - δ`, using the closed window
   at `u - δ ∈ (T, u)`).

**(4)** Conclusion: `G = Icc T 0`.  `sInf G ∈ G` (`IsClosed.csInf_mem`; `G` is nonempty, closed by (2)
and bounded below by `T`); if `sInf G > T` then (3) produces `sInf G - δ ∈ G`, contradicting the
infimum; so `sInf G = T ∈ G`, and `T ∈ G` is exactly the conclusion.

The two lemmas under this file (`Work.Drive.N2.norm_Z_eq_of_hZ`, `Work.Drive.N2.norm_four_eq`,
`Work.Drive.N2.im_ge_of_notMem_interior`, `Work.Drive.N2.im_sq_eq_of_flow_Icc` and
`Work.Drive.N2.notMem_modelBall_home`) are the pieces of the argument above; the last one is the
classical maximal-source brick and is stated independently of the chart family `φ`.

Do NOT weaken the conclusion at the endpoint `u = T` (the transport needs it there); it is covered by
the closedness (2).  Do NOT drop `hRpos` or `hfcont`: both counterexamples are on disk.
-/

/-- **The complex coordinate of a chart carries the chart's norm.** -/
lemma norm_Z_eq_of_hZ {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Z : M → ℂ)
    (hZ : ∀ m : M, Z m = ((φ m 0 : ℝ) : ℂ) + ((φ m 1 : ℝ) : ℂ) * Complex.I) (m : M) :
    ‖Z m‖ = ‖φ m‖ := by
  have h1 : ‖Z m‖ ^ 2 = (φ m 0) ^ 2 + (φ m 1) ^ 2 := by
    rw [hZ m, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one]
    ring
  have h2 : (φ m 0) ^ 2 + (φ m 1) ^ 2 = ‖φ m‖ ^ 2 := norm_uVec (φ m)
  nlinarith [norm_nonneg (Z m), norm_nonneg (φ m), h1, h2]

/-- `‖w‖ ^ 4` in terms of the real and imaginary parts of `w ^ 2`. -/
lemma norm_four_eq (w : ℂ) : ‖w‖ ^ 4 = (w ^ 2).re ^ 2 + (w ^ 2).im ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← norm_pow w 2, Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- **The cutting step.**  A point of a chart source whose value lies in the *open* window and which
is not in the interior of the box `{|Re (Z ·)²| ≤ η ∧ |Im (Z ·)²| ≤ c₀}` has invariant at least
`c₀`. -/
lemma im_ge_of_notMem_interior {M : Type*} [TopologicalSpace M] {f : M → ℝ} {Z : M → ℂ}
    {U : Set M} {c η c₀ : ℝ}
    (hZc : ∀ x ∈ U, ContinuousAt Z x) (hlev : ∀ x ∈ U, f x = c + ((Z x) ^ 2).re)
    {x : M} (hxU : x ∈ U) (hband : f x ∈ Set.Ioo (c - η) (c + η))
    (hxD : x ∉ interior {y : M | |((Z y) ^ 2).re| ≤ η ∧ |((Z y) ^ 2).im| ≤ c₀}) :
    c₀ ≤ |((Z x) ^ 2).im| := by
  by_contra hlt
  rw [not_le] at hlt
  have hre : |((Z x) ^ 2).re| < η := by
    have h1 : |f x - c| < η := by
      rw [abs_lt]
      exact ⟨by linarith [hband.1], by linarith [hband.2]⟩
    have h2 : ((Z x) ^ 2).re = f x - c := by linarith [hlev x hxU]
    rw [h2]; exact h1
  have hZct := hZc x hxU
  have hsq : ContinuousAt (fun y : M => (Z y) ^ 2) x := hZct.pow 2
  have hre_c : ContinuousAt (fun y : M => |((Z y) ^ 2).re|) x :=
    (Complex.continuous_re.continuousAt.comp hsq).abs
  have him_c : ContinuousAt (fun y : M => |((Z y) ^ 2).im|) x :=
    (Complex.continuous_im.continuousAt.comp hsq).abs
  have hpair : ContinuousAt (fun y : M => (|((Z y) ^ 2).re|, |((Z y) ^ 2).im|)) x :=
    hre_c.prodMk him_c
  have hopen : IsOpen {v : ℝ × ℝ | v.1 < η ∧ v.2 < c₀} :=
    (isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_snd continuous_const)
  have hnhds : {y : M | |((Z y) ^ 2).re| ≤ η ∧ |((Z y) ^ 2).im| ≤ c₀} ∈ 𝓝 x := by
    refine Filter.mem_of_superset (hpair.preimage_mem_nhds (hopen.mem_nhds ⟨hre, hlt⟩)) ?_
    intro y hy
    exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  exact hxD (mem_interior_iff_mem_nhds.mpr hnhds)

/-- The half-open interval `Ico a b` is a neighbourhood of `b` from the left. -/
lemma Ico_mem_nhdsWithin {a b : ℝ} (h : a < b) : Set.Ico a b ∈ 𝓝[<] b := by
  have h1 : Set.Ici a ∈ 𝓝[<] b := nhdsWithin_le_nhds (Ici_mem_nhds h)
  exact Filter.mem_of_superset (Filter.inter_mem h1 self_mem_nhdsWithin) (fun x hx => hx)

/-- **The conservation of `Im (Z ·)²` along a source-confined piece of a trajectory.** -/
lemma im_sq_eq_of_flow_Icc {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {Φ : ℝ × M → M} (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (Z : M → ℂ) (hZ : ∀ m : M, Z m = ((φ m 0 : ℝ) : ℂ) + ((φ m 1 : ℝ) : ℂ) * Complex.I)
    (r : ℝ)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ φ.source) →
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 0)
        (chartMult r (‖φ (Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 1)
        (chartMult r (‖φ (Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ (Φ (t, y)) 1)) t)
    (hΦ0 : ∀ m : M, Φ (0, m) = m)
    (hcomp : ∀ (s t : ℝ) (y : M), Φ (s, Φ (t, y)) = Φ (s + t, y))
    {x : M} {a b : ℝ} (hab : a ≤ b)
    (hconf : ∀ σ ∈ Set.Icc a b, Φ (σ, x) ∈ φ.source) :
    ((Z (Φ (b, x))) ^ 2).im = ((Z (Φ (a, x))) ^ 2).im := by
  have hb1 : ∀ u ∈ Set.Icc (min 0 (b - a)) (max 0 (b - a)), Φ (u, Φ (a, x)) ∈ φ.source := by
    intro u hu
    rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hu
    rw [hcomp u a x]
    exact hconf (u + a) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h := im_sq_eq_of_flow_chartODE Φ φ Z hZ r hODE hΦ0 (Φ (a, x)) (b - a) hb1
  rw [hcomp (b - a) a x, show b - a + a = b from by ring] at h
  exact h

/-- **The home chart's model ball is never visited.**  If a piece `[w, 0]` of the trajectory
`σ ↦ Φ (σ, x₀)` has values in the closed window `[c - η, c + η]`, then its initial point is outside
the home chart's model ball `{‖φ ·‖ < r}` — provided `r⁴ < ρ⁴ - η²`, which is the entry bound at
the chart source boundary `‖Z ·‖ = ρ` (with `r` the model ball's radius and `c₀ > r²` the invariant
threshold of the off-box point `x₀`).

The proof follows the trajectory backwards from `x₀`: let `A` be the set of parameters `v` for which
`[w, v]` is confined to the chart source and `β = sSup (A ∩ [w, 0])`.  Either the trajectory is in
the source all the way up to `0` — then `x₀` is in the source and the invariant `c₀ ≤ |Im (Z x₀)²|`
is conserved down to `w` — or it leaves the source at `β`, where `‖Z ·‖ = ρ` and the value is windowed
(`|Re| ≤ η` so `|Im|² ≥ ρ⁴ - η² > r⁴`), and the same bound is transferred to `w` by conservation
below `β` and continuity at `β`. -/
theorem notMem_modelBall_home {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {f : M → ℝ} {Φ : ℝ × M → M} {Z : M → ℂ}
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ)
    {c η c₀ ρ : ℝ} (hr : 0 < r) (hrc : r ^ 2 < c₀)
    (hZ : ∀ m : M, Z m = ((φ m 0 : ℝ) : ℂ) + ((φ m 1 : ℝ) : ℂ) * Complex.I)
    (hZcont : Continuous Z)
    (hvalj : ∀ y ∈ φ.source, f y = c + ((Z y) ^ 2).re)
    (hfcont : Continuous f)
    {x₀ : M} (horbit : Continuous fun u : ℝ => Φ (u, x₀))
    (hcons : ∀ a b : ℝ, a ≤ b → (∀ σ ∈ Set.Icc a b, Φ (σ, x₀) ∈ φ.source) →
      ((Z (Φ (b, x₀))) ^ 2).im = ((Z (Φ (a, x₀))) ^ 2).im)
    (hΦ0 : ∀ y : M, Φ (0, y) = y)
    (hsource : ∀ z : M, z ∈ φ.source ↔ ‖Z z‖ < ρ)
    (hwin : f x₀ ∈ Set.Ioo (c - η) (c + η))
    (hD : x₀ ∉ interior {y : M | |((Z y) ^ 2).re| ≤ η ∧ |((Z y) ^ 2).im| ≤ c₀})
    (h4ρ : r ^ 4 < ρ ^ 4 - η ^ 2)
    {w : ℝ} (hw0 : w ≤ 0)
    (hval : ∀ σ ∈ Set.Icc w 0, f (Φ (σ, x₀)) ∈ Set.Icc (c - η) (c + η)) :
    Φ (w, x₀) ∉ modelBall φ r := by
  intro hz
  have hzsrc : Φ (w, x₀) ∈ φ.source := hz.1
  have hc0 : 0 < c₀ := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ r ^ 2) hrc
  -- the parameter set on which the trajectory is confined to the chart source
  set A : Set ℝ := {v : ℝ | ∀ u' ∈ Set.Icc w v, Φ (u', x₀) ∈ φ.source} with hAdef
  set B : Set ℝ := A ∩ Set.Icc w 0 with hBdef
  set β : ℝ := sSup B with hβdef
  have hwA : w ∈ A := by
    rw [hAdef]
    intro u' hu'
    rw [Set.Icc_self] at hu'
    rw [hu']
    exact hzsrc
  have hwB : w ∈ B := by rw [hBdef]; exact ⟨hwA, ⟨le_rfl, hw0⟩⟩
  have hBne : B.Nonempty := ⟨w, hwB⟩
  have hBbdd : BddAbove B := ⟨0, fun b hb => by rw [hBdef] at hb; exact hb.2.2⟩
  have hβle : β ≤ 0 := by
    rw [hβdef]
    exact csSup_le hBne (fun b hb => by rw [hBdef] at hb; exact hb.2.2)
  have hwβ : w ≤ β := by
    rw [hβdef]; exact le_csSup hBbdd hwB
  have hltβ : ∀ v ∈ Set.Ico w β, Φ (v, x₀) ∈ φ.source := by
    intro v hv
    obtain ⟨b, hb, hvb⟩ := (lt_csSup_iff hBbdd hBne).mp hv.2
    rw [hBdef] at hb
    exact hb.1 v ⟨hv.1, le_of_lt hvb⟩
  have hcons' : ∀ v ∈ Set.Ico w β, ((Z (Φ (v, x₀))) ^ 2).im = ((Z (Φ (w, x₀))) ^ 2).im := by
    intro v hv
    exact hcons w v hv.1 (fun σ hσ => hltβ σ ⟨hσ.1, lt_of_le_of_lt hσ.2 hv.2⟩)
  have hgoal : r ^ 4 < (((Z (Φ (w, x₀))) ^ 2).im) ^ 2 := by
    by_cases hβsrc : Φ (β, x₀) ∈ φ.source
    · -- case 1: the trajectory is confined to the source all the way to `0`
      have hβAf : ∀ u' ∈ Set.Icc w β, Φ (u', x₀) ∈ φ.source := by
        intro u' hu'
        rcases lt_or_eq_of_le hu'.2 with hlt | heq
        · exact hltβ u' ⟨hu'.1, hlt⟩
        · rw [heq]; exact hβsrc
      have hβB : β ∈ B := by rw [hBdef]; exact ⟨by rw [hAdef]; exact hβAf, ⟨hwβ, hβle⟩⟩
      have hβ0 : β = 0 := by
        by_contra hne
        have hβneg : β < 0 := lt_of_le_of_ne hβle hne
        have hnhd : {σ : ℝ | Φ (σ, x₀) ∈ φ.source} ∈ 𝓝 β :=
          horbit.continuousAt.preimage_mem_nhds (φ.open_source.mem_nhds hβsrc)
        obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hnhd
        set ε' : ℝ := min (ε / 2) ((-β) / 2) with hε'def
        have hε'pos : 0 < ε' := lt_min (by linarith) (by linarith)
        have hε'ε : ε' < ε := by
          have h1 : ε' ≤ ε / 2 := min_le_left (ε / 2) ((-β) / 2)
          linarith
        have hε'β : ε' ≤ (-β) / 2 := min_le_right _ _
        have hmem : β + ε' ∈ B := by
          rw [hBdef]
          refine ⟨?_, ?_⟩
          · rw [hAdef]
            intro u' hu'
            rcases lt_or_ge u' β with h | h
            · exact hβAf u' ⟨hu'.1, le_of_lt h⟩
            · refine hε ?_
              rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs,
                abs_of_nonneg (by linarith : (0 : ℝ) ≤ u' - β)]
              linarith [hu'.2]
          · constructor <;> linarith
        have hle : β + ε' ≤ β := le_csSup hBbdd hmem
        linarith
      have h0B : 0 ∈ B := hβ0 ▸ hβB
      have hsrc0 : ∀ σ ∈ Set.Icc w 0, Φ (σ, x₀) ∈ φ.source := by
        rw [hBdef, hAdef] at h0B
        exact fun σ hσ => h0B.1 σ hσ
      have hx0src : x₀ ∈ φ.source := by
        have h0 := hsrc0 0 ⟨hw0, le_rfl⟩
        rwa [hΦ0 x₀] at h0
      have hIm0 : c₀ ≤ |((Z x₀) ^ 2).im| :=
        im_ge_of_notMem_interior (fun _ _ => hZcont.continuousAt)
          (fun y hy => hvalj y hy) hx0src hwin hD
      have hconsw0 : ((Z (Φ (w, x₀))) ^ 2).im = ((Z x₀) ^ 2).im := by
        have h := hcons w 0 hw0 hsrc0
        rw [hΦ0 x₀] at h
        exact h.symm
      have h2 : c₀ ^ 2 ≤ ((Z x₀) ^ 2).im ^ 2 := by
        have h := mul_self_le_mul_self (le_of_lt hc0) hIm0
        rw [← sq, ← sq, sq_abs] at h
        exact h
      have h3 : r ^ 4 < c₀ ^ 2 := by
        have h := pow_lt_pow_left₀ hrc (by positivity : (0 : ℝ) ≤ r ^ 2) (by norm_num : (2:ℕ) ≠ 0)
        nlinarith [h]
      rw [hconsw0]
      linarith
    · -- case 2: the trajectory leaves the source at `β`
      have hβne : β ≠ w := by
        intro h
        rw [h] at hβsrc
        exact hβsrc hzsrc
      have hwβ' : w < β := lt_of_le_of_ne hwβ (Ne.symm hβne)
      have hρβ : ‖Z (Φ (β, x₀))‖ = ρ := by
        refine le_antisymm ?_ ?_
        · have htend : Tendsto (fun σ : ℝ => ‖Z (Φ (σ, x₀))‖) (𝓝[<] β) (𝓝 ‖Z (Φ (β, x₀))‖) :=
            ((hZcont.comp horbit).norm.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
          refine le_of_tendsto htend ?_
          exact Filter.mem_of_superset (Ico_mem_nhdsWithin hwβ')
            (fun σ hσ => le_of_lt ((hsource (Φ (σ, x₀))).mp (hltβ σ hσ)))
        · by_contra hlt
          rw [not_le] at hlt
          exact hβsrc ((hsource (Φ (β, x₀))).mpr hlt)
      have hReβ : ((Z (Φ (β, x₀))) ^ 2).re = f (Φ (β, x₀)) - c := by
        have hc : Continuous fun σ : ℝ => ((Z (Φ (σ, x₀))) ^ 2).re :=
          Complex.continuous_re.comp ((hZcont.comp horbit).pow 2)
        have ht1 : Tendsto (fun σ : ℝ => f (Φ (σ, x₀))) (𝓝[<] β) (𝓝 (f (Φ (β, x₀)))) :=
          ((hfcont.comp horbit).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        have ht2 : Tendsto (fun σ : ℝ => c + ((Z (Φ (σ, x₀))) ^ 2).re) (𝓝[<] β)
            (𝓝 (c + ((Z (Φ (β, x₀))) ^ 2).re)) :=
          ((continuous_const.add hc).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        have heq : (fun σ : ℝ => f (Φ (σ, x₀))) =ᶠ[𝓝[<] β]
            fun σ : ℝ => c + ((Z (Φ (σ, x₀))) ^ 2).re :=
          Filter.mem_of_superset (Ico_mem_nhdsWithin hwβ')
            (fun σ hσ => hvalj (Φ (σ, x₀)) (hltβ σ hσ))
        have huniq := tendsto_nhds_unique ht1 (ht2.congr' heq.symm)
        linarith
      have hRele : |((Z (Φ (β, x₀))) ^ 2).re| ≤ η := by
        have hb := hval β ⟨hwβ, hβle⟩
        rw [hReβ]
        exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
      have hImβ : r ^ 4 < (((Z (Φ (β, x₀))) ^ 2).im) ^ 2 := by
        have hn4 := norm_four_eq (Z (Φ (β, x₀)))
        rw [hρβ] at hn4
        have hre2 : ((Z (Φ (β, x₀))) ^ 2).re ^ 2 ≤ η ^ 2 := by
          have h := mul_self_le_mul_self (abs_nonneg ((Z (Φ (β, x₀))) ^ 2).re) hRele
          rw [← sq, ← sq, sq_abs] at h
          exact h
        nlinarith [hn4, hre2, h4ρ]
      have hImw : ((Z (Φ (w, x₀))) ^ 2).im = ((Z (Φ (β, x₀))) ^ 2).im := by
        have hc : Continuous fun σ : ℝ => ((Z (Φ (σ, x₀))) ^ 2).im :=
          Complex.continuous_im.comp ((hZcont.comp horbit).pow 2)
        have htend : Tendsto (fun σ : ℝ => ((Z (Φ (σ, x₀))) ^ 2).im) (𝓝[<] β)
            (𝓝 (((Z (Φ (β, x₀))) ^ 2).im)) :=
          (hc.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        have heq : (fun σ : ℝ => ((Z (Φ (σ, x₀))) ^ 2).im) =ᶠ[𝓝[<] β]
            fun _ : ℝ => ((Z (Φ (w, x₀))) ^ 2).im :=
          Filter.mem_of_superset (Ico_mem_nhdsWithin hwβ') (fun σ hσ => hcons' σ hσ)
        have hconst : Tendsto (fun σ : ℝ => ((Z (Φ (σ, x₀))) ^ 2).im) (𝓝[<] β)
            (𝓝 (((Z (Φ (w, x₀))) ^ 2).im)) :=
          tendsto_const_nhds.congr' heq.symm
        exact (tendsto_nhds_unique htend hconst).symm
      rw [hImw]
      exact hImβ
  -- the contradiction with `z ∈ modelBall φ r`
  have hZn : ‖Z (Φ (w, x₀))‖ = ‖φ (Φ (w, x₀))‖ := norm_Z_eq_of_hZ φ Z hZ _
  have h4 : r ^ 4 < ‖Z (Φ (w, x₀))‖ ^ 4 := by
    rw [norm_four_eq]
    nlinarith [hgoal, sq_nonneg ((Z (Φ (w, x₀))) ^ 2).re]
  rw [hZn] at h4
  have hfin : r < ‖φ (Φ (w, x₀))‖ :=
    (pow_lt_pow_iff_left₀ (le_of_lt hr) (norm_nonneg _) (by norm_num)).mp h4
  exact absurd hz.2 (not_lt.mpr hfin.le)

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

/-- **The legality of the saddle-window transport.** -/
theorem saddleJourneyAvoidsBalls {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {Φ : ℝ × M → M} {ι : Type*} [Fintype ι] (j : ι)
    {x : ι → M} {φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    {r : ι → ℝ} {c η c₀ R : ℝ} {Z : M → ℂ}
    (hfcont : Continuous f)
    (hη : 0 < η) (hr : ∀ i, 0 < r i) (hRpos : 0 < R)
    (hR : η ^ 2 + (r j) ^ 4 < R ^ 4)
    (hZ : ∀ m : M, Z m = ((φ j m 0 : ℝ) : ℂ) + ((φ j m 1 : ℝ) : ℂ) * Complex.I)
    (hZcont : Continuous Z)
    (hvalj : ∀ y ∈ (φ j).source, f y = c + ((Z y) ^ 2).re)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ (φ j).source) →
      HasDerivAt (fun σ : ℝ => φ j (Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult (r j) (‖φ j (Φ (t, y))‖ ^ 2) * ((1 : ℝ) * φ j (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ j (Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult (r j) (‖φ j (Φ (t, y))‖ ^ 2) * ((-1 : ℝ) * φ j (Φ (t, y)) 1)) t)
    (hΦ0 : ∀ y : M, Φ (0, y) = y)
    (hcomp : ∀ (s t : ℝ) (y : M), Φ (s, Φ (t, y)) = Φ (s + t, y))
    {x₀ : M} (horbit : Continuous fun u : ℝ => Φ (u, x₀))
    {ρ : ℝ} (hρR : R < ρ)
    (hsource : ∀ z : M, z ∈ (φ j).source ↔ ‖Z z‖ < ρ)
    (hsep : ∀ i : ι, i ≠ j → ∀ z : M, z ∈ Work.Drive.N2.modelBall (φ i) (r i) → η < |f z - c|)
    (hlevel : ∀ (y : M) (t : ℝ), (∀ i, y ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i, Φ (u, y) ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
      f (Φ (t, y)) = f y + t)
    (hwin : f x₀ ∈ Set.Ioo (c - η) (c + η))
    (hD : x₀ ∉ interior {y : M | |((Z y) ^ 2).re| ≤ η ∧ |((Z y) ^ 2).im| ≤ c₀})
    (hrc : (r j) ^ 2 < c₀) :
    ∀ u ∈ Set.Icc (min 0 (c - η - f x₀)) (max 0 (c - η - f x₀)),
      ∀ i : ι, Φ (u, x₀) ∉ Work.Drive.N2.modelBall (φ i) (r i) := by
  have hrj : 0 < r j := hr j
  have hR4 : η ^ 2 + (r j) ^ 4 < ρ ^ 4 := by
    have h : R ^ 4 < ρ ^ 4 := pow_lt_pow_left₀ hρR (le_of_lt hRpos) (by norm_num)
    linarith
  have h4ρ : (r j) ^ 4 < ρ ^ 4 - η ^ 2 := by linarith
  have hT0 : c - η - f x₀ < 0 := by linarith [hwin.1]
  have hcons : ∀ a b : ℝ, a ≤ b → (∀ σ ∈ Set.Icc a b, Φ (σ, x₀) ∈ (φ j).source) →
      ((Z (Φ (b, x₀))) ^ 2).im = ((Z (Φ (a, x₀))) ^ 2).im :=
    fun a b hab hc => im_sq_eq_of_flow_Icc (φ j) Z hZ (r j) hODE hΦ0 hcomp hab hc
  -- **(0)** the starting point is off every model ball
  have hx0 : ∀ i : ι, x₀ ∉ modelBall (φ i) (r i) := by
    intro i
    by_cases hij : i = j
    · rw [hij]
      intro hmem
      have hIm0 : c₀ ≤ |((Z x₀) ^ 2).im| :=
        im_ge_of_notMem_interior (fun _ _ => hZcont.continuousAt) (fun y hy => hvalj y hy)
          hmem.1 hwin hD
      have hc0 : 0 < c₀ := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ (r j) ^ 2) hrc
      have h2 : c₀ ^ 2 ≤ ((Z x₀) ^ 2).im ^ 2 := by
        have h := mul_self_le_mul_self (le_of_lt hc0) hIm0
        rw [← sq, ← sq, sq_abs] at h
        exact h
      have h3 : (r j) ^ 4 < c₀ ^ 2 := by
        have h := pow_lt_pow_left₀ hrc (by positivity : (0 : ℝ) ≤ (r j) ^ 2) (by norm_num : (2:ℕ) ≠ 0)
        nlinarith [h]
      have h4 : (r j) ^ 4 < ‖Z x₀‖ ^ 4 := by
        rw [norm_four_eq]
        nlinarith [h2, h3, sq_nonneg ((Z x₀) ^ 2).re]
      rw [norm_Z_eq_of_hZ (φ j) Z hZ x₀] at h4
      have hfin : r j < ‖φ j x₀‖ :=
        (pow_lt_pow_iff_left₀ (le_of_lt hrj) (norm_nonneg _) (by norm_num)).mp h4
      linarith [hmem.2]
    · intro hmem
      have h1 := hsep i hij x₀ hmem
      have h2 : |f x₀ - c| < η := by
        rw [abs_lt]; exact ⟨by linarith [hwin.1], by linarith [hwin.2]⟩
      linarith
  -- the good prefix set `G`
  set G : Set ℝ := {u : ℝ | u ∈ Set.Icc (c - η - f x₀) 0 ∧
    ∀ w ∈ Set.Icc u 0, ∀ i : ι, Φ (w, x₀) ∉ modelBall (φ i) (r i)} with hGdef
  have hGmem : ∀ u : ℝ, u ∈ G ↔ (u ∈ Set.Icc (c - η - f x₀) 0 ∧
      ∀ w ∈ Set.Icc u 0, ∀ i : ι, Φ (w, x₀) ∉ modelBall (φ i) (r i)) := by
    intro u
    simp only [hGdef, Set.mem_setOf_eq]
  have hG0 : 0 ∈ G := by
    refine (hGmem 0).mpr ⟨⟨le_of_lt hT0, le_rfl⟩, ?_⟩
    intro w hw i
    rw [Set.Icc_self] at hw
    rw [hw, hΦ0 x₀]
    exact hx0 i
  have hGne : G.Nonempty := ⟨0, hG0⟩
  have hGbdd : BddBelow G := ⟨c - η - f x₀, fun u hu => ((hGmem u).mp hu).1.1⟩
  -- **(2)** `G` is closed
  have hBallOpen : ∀ i : ι, IsOpen (modelBall (φ i) (r i)) := by
    intro i
    have h := (φ i).isOpen_inter_preimage
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (r i)))
    have h2 : modelBall (φ i) (r i)
        = (φ i).source ∩ (φ i) ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (r i) := by
      ext y
      simp [modelBall, Metric.mem_ball, dist_eq_norm]
    rw [h2]
    exact h
  have hGclosed : IsClosed G := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro u hu
    by_cases huI : u ∈ Set.Icc (c - η - f x₀) 0
    · have hwit : ∃ w ∈ Set.Icc u 0, ∃ i : ι, Φ (w, x₀) ∈ modelBall (φ i) (r i) := by
        by_contra h
        exact hu ((hGmem u).mpr ⟨huI, fun w hw i hmem => h ⟨w, hw, i, hmem⟩⟩)
      obtain ⟨w, hw, i, hi⟩ := hwit
      rcases lt_or_eq_of_le hw.1 with hlt | heq
      · refine Filter.mem_of_superset
          (isOpen_Ioo.mem_nhds (show u ∈ Set.Ioo (2 * u - w) w from ⟨by linarith, hlt⟩)) ?_
        intro u' hu'
        intro hu'G
        exact ((hGmem u').mp hu'G).2 w ⟨le_of_lt hu'.2, hw.2⟩ i hi
      · have hi' : Φ (u, x₀) ∈ modelBall (φ i) (r i) := by rw [heq]; exact hi
        have hnhd : {σ : ℝ | Φ (σ, x₀) ∈ modelBall (φ i) (r i)} ∈ 𝓝 u :=
          horbit.continuousAt.preimage_mem_nhds ((hBallOpen i).mem_nhds hi')
        obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hnhd
        refine Filter.mem_of_superset (Metric.ball_mem_nhds u hεpos) ?_
        intro u' hu'
        intro hu'G
        by_cases hI : u' ∈ Set.Icc (c - η - f x₀) 0
        · exact ((hGmem u').mp hu'G).2 u' ⟨le_rfl, hI.2⟩ i (hε hu')
        · exact hI ((hGmem u').mp hu'G).1
    · exact Filter.mem_of_superset
        ((isClosed_Icc (a := c - η - f x₀) (b := 0)).isOpen_compl.mem_nhds (by simpa using huI))
        (fun u' hu' hu'G => hu' ((hGmem u').mp hu'G).1)
  have hsInf_mem : sInf G ∈ G := hGclosed.csInf_mem hGne hGbdd
  -- **(3)** the openness step
  have hopen : ∀ u ∈ G, c - η - f x₀ < u → ∃ δ > 0, u - δ ∈ G := by
    intro u huG hTu
    have huI : u ∈ Set.Icc (c - η - f x₀) 0 := ((hGmem u).mp huG).1
    have hu0 : u ≤ 0 := huI.2
    have huv : ∀ σ ∈ Set.Icc u 0, ∀ i : ι, Φ (σ, x₀) ∉ modelBall (φ i) (r i) :=
      ((hGmem u).mp huG).2
    have hlevu : ∀ σ ∈ Set.Icc u 0, f (Φ (σ, x₀)) = f x₀ + σ := by
      intro σ hσ
      have hσ0 : σ ≤ 0 := hσ.2
      refine hlevel x₀ σ (hx0) ?_
      intro σ' hσ'
      have hmem : σ' ∈ Set.Icc u 0 := by
        rw [min_eq_right hσ0, max_eq_left hσ0] at hσ'
        exact ⟨le_trans hσ.1 hσ'.1, hσ'.2⟩
      exact huv σ' hmem
    have hvalu : f (Φ (u, x₀)) ∈ Set.Ioo (c - η) (c + η) := by
      have h := hlevu u ⟨le_rfl, hu0⟩
      rw [h]
      exact ⟨by linarith [hTu], by linarith [hwin.2, hu0]⟩
    have hnhd : {σ : ℝ | f (Φ (σ, x₀)) ∈ Set.Ioo (c - η) (c + η)} ∈ 𝓝 u :=
      ((hfcont.comp horbit).continuousAt).preimage_mem_nhds (isOpen_Ioo.mem_nhds hvalu)
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.mem_nhds_iff.mp hnhd
    have hδpos : 0 < min (δ₀ / 2) ((u - (c - η - f x₀)) / 2) :=
      lt_min (by linarith) (by linarith)
    refine ⟨min (δ₀ / 2) ((u - (c - η - f x₀)) / 2), hδpos, ?_⟩
    have hδ₁ : min (δ₀ / 2) ((u - (c - η - f x₀)) / 2) < δ₀ := by
      have h := min_le_left (δ₀ / 2) ((u - (c - η - f x₀)) / 2); linarith
    have hδ₂ : min (δ₀ / 2) ((u - (c - η - f x₀)) / 2) ≤ (u - (c - η - f x₀)) / 2 :=
      min_le_right _ _
    have hvalbd : ∀ σ ∈ Set.Icc (u - min (δ₀ / 2) ((u - (c - η - f x₀)) / 2)) 0,
        f (Φ (σ, x₀)) ∈ Set.Icc (c - η) (c + η) := by
      intro σ hσ
      rcases lt_or_ge u σ with h | h
      · have h1 := hlevu σ ⟨le_of_lt h, hσ.2⟩
        rw [h1]
        exact ⟨by linarith [hσ.1, hδ₂, hTu], by linarith [hwin.2, hσ.2]⟩
      · have hdist : dist σ u < δ₀ := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith : σ - u ≤ 0)]
          linarith [hσ.1, hδ₁]
        exact ⟨le_of_lt (hδ₀ hdist).1, le_of_lt (hδ₀ hdist).2⟩
    refine (hGmem _).mpr ⟨⟨by linarith [hδ₂, hTu], by linarith [hδpos, hu0]⟩, ?_⟩
    intro w hw i
    by_cases hij : i = j
    · rw [hij]
      by_contra hmem
      exact notMem_modelBall_home (φ j) (r j) hrj hrc hZ hZcont hvalj hfcont horbit hcons hΦ0
        hsource hwin hD h4ρ hw.2 (fun σ hσ => hvalbd σ ⟨le_trans hw.1 hσ.1, hσ.2⟩) hmem
    · intro hmem
      have h1 := hsep i hij (Φ (w, x₀)) hmem
      have h3 := hvalbd w hw
      have h2 : |f (Φ (w, x₀)) - c| ≤ η :=
        abs_le.mpr ⟨by linarith [h3.1], by linarith [h3.2]⟩
      linarith
  -- **(4)** conclusion
  have hsInf_eq : sInf G = c - η - f x₀ := by
    by_contra hne
    have hTs : c - η - f x₀ ≤ sInf G := le_csInf hGne (fun b hb => ((hGmem b).mp hb).1.1)
    have hlt : c - η - f x₀ < sInf G := lt_of_le_of_ne hTs (Ne.symm hne)
    obtain ⟨δ, hδpos, hδG⟩ := hopen (sInf G) hsInf_mem hlt
    have hle : sInf G ≤ sInf G - δ := csInf_le hGbdd hδG
    linarith
  have hTmem : c - η - f x₀ ∈ G := by
    rw [← hsInf_eq]; exact hsInf_mem
  have hmin : min 0 (c - η - f x₀) = c - η - f x₀ := min_eq_right hT0.le
  have hmax : max 0 (c - η - f x₀) = 0 := max_eq_left hT0.le
  intro u hu i
  rw [hmin, hmax] at hu
  exact ((hGmem (c - η - f x₀)).mp hTmem).2 u hu i

end Work.Drive.N2
