import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.pCoreSeries_mono
import Submission.Work.Fitting.isPSolvable_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.isPSolvable_subgroup`

`p`-solvability passes to subgroups: if `G` is a finite `p`-solvable group then so is every
subgroup `H ≤ G`.

The proof intersects the upper `p`-series `1 = O_0(G) ≤ O_1(G) ≤ ...` of `G` with `H`.
The resulting chain `1 ≤ H ∩ O_1(G) ≤ H ∩ O_2(G) ≤ ...` consists of subgroups normal in `H`
whose successive quotients embed into `O_{n+1}(G)/O_n(G)`; the latter is a `p'`-group for
even `n` and a `p`-group for odd `n`.  Since the upper `p`-series of `H` dominates every
normal series with `p`- and `p'`-steps, `H ∩ O_n(G) ≤ O_n(H)` for all `n`; taking `n` with
`O_n(G) = G` (which exists because `G` is `p`-solvable) gives `O_n(H) = H`.
-/

set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.Fitting

variable {G : Type*} [Group G]

/-- The type of `π`-number occurring at step `n` of a `p`-series: the `n`-th step is a
`p'`-step for even `n` and a `p`-step for odd `n`, matching `pCoreSeries_succ`. -/
def stepPi (p : ℕ) (n : ℕ) : ℕ → Prop := fun q => if Even n then q ≠ p else q = p

/-- **Growth of the upper `p`-series.**  If `N ◁ M ◁ K`, `N` is contained in the `n`-th term
of the upper `p`-series of `K`, and `M/N` is a `p'`-group for even `n` (a `p`-group for odd
`n`), then `M` is contained in the `(n+1)`-st term. -/
theorem le_pCoreSeries_succ (p : ℕ) (K : Type*) [Group K] [Finite K] (n : ℕ)
    {N M : Subgroup K} (hNn : N.Normal) (hMn : M.Normal) (_hNM : N ≤ M)
    (hN : N ≤ pCoreSeries p K n)
    (hcard : IsPiNat (stepPi p n) (N.relIndex M)) :
    M ≤ pCoreSeries p K (n + 1) := by
  haveI : N.Normal := hNn
  haveI : M.Normal := hMn
  haveI : (pCoreSeries p K n).Normal := pCoreSeries_normal p K n
  rw [pCoreSeries_succ]
  intro x hx
  rw [Subgroup.mem_comap]
  -- The image of `M` in `K/N` is a normal `π`-subgroup, hence lies in `O_π(K/N)`.
  have hMN : M.map (QuotientGroup.mk' N) ≤ piCore (stepPi p n) (K ⧸ N) := by
    refine le_piCore (hMn.map _ (QuotientGroup.mk'_surjective N)) ?_
    rw [← Subgroup.relIndex_ker M (QuotientGroup.mk' N), QuotientGroup.ker_mk']
    exact hcard
  have hxN : (QuotientGroup.mk' N) x ∈ piCore (stepPi p n) (K ⧸ N) :=
    hMN (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  set q : K ⧸ N →* K ⧸ pCoreSeries p K n :=
    QuotientGroup.map N (pCoreSeries p K n) (MonoidHom.id K) (by simpa using hN) with hq
  have hqsurj : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective N (pCoreSeries p K n) (MonoidHom.id K)
      (by simpa [Function.comp_def] using (QuotientGroup.mk_surjective (s := pCoreSeries p K n)))
      (by simpa using hN)
  have hcore : piCore (stepPi p n) (K ⧸ N) ≤
      (piCore (stepPi p n) (K ⧸ pCoreSeries p K n)).comap q :=
    Subgroup.map_le_iff_le_comap.mp (piCore_map_le (π := stepPi p n) q hqsurj)
  have hmem : q ((QuotientGroup.mk' N) x) ∈ piCore (stepPi p n) (K ⧸ pCoreSeries p K n) :=
    hcore hxN
  rw [hq, QuotientGroup.map_mk'] at hmem
  exact hmem

/-- The `n`-th term of the upper `p`-series of `G`, pulled back to a subgroup `H ≤ G`. -/
def subSeries (p : ℕ) (G : Type*) [Group G] (H : Subgroup G) (n : ℕ) : Subgroup H :=
  (pCoreSeries p G n).comap H.subtype

/-- The successive quotients of the intersection of the upper `p`-series of `G` with `H`
are `p'`-groups (even step) or `p`-groups (odd step): they embed into the corresponding
factors of the upper `p`-series of `G`. -/
theorem subSeries_relIndex_isPiNat (p : ℕ) (G : Type*) [Group G] [Finite G]
    (H : Subgroup G) (n : ℕ) :
    IsPiNat (stepPi p n) ((subSeries p G H n).relIndex (subSeries p G H (n + 1))) := by
  haveI : (pCoreSeries p G n).Normal := pCoreSeries_normal p G n
  set φ : H →* G ⧸ pCoreSeries p G n :=
    (QuotientGroup.mk' (pCoreSeries p G n)).comp H.subtype with hφdef
  have hker : φ.ker = subSeries p G H n := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, hφdef, subSeries, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  -- The image of `H ∩ O_{n+1}(G)` in `G/O_n(G)` lies in `O_π(G/O_n(G))`.
  have hle : (subSeries p G H (n + 1)).map φ ≤ piCore (stepPi p n) (G ⧸ pCoreSeries p G n) := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    exact hx
  -- `relIndex` of the intersection series equals the cardinal of this image.
  have hcard : (subSeries p G H n).relIndex (subSeries p G H (n + 1)) =
      Nat.card ↥((subSeries p G H (n + 1)).map φ) := by
    rw [← hker]
    exact Subgroup.relIndex_ker _ φ
  rw [hcard]
  exact isPiNat_of_dvd (Subgroup.card_dvd_of_le hle)
    (piCore_isPiNat (G ⧸ pCoreSeries p G n) (stepPi p n))

/-- The upper `p`-series of `G`, intersected with `H`, is dominated by the upper `p`-series
of `H`. -/
theorem comap_pCoreSeries_le (p : ℕ) (G : Type*) [Group G] [Finite G] (H : Subgroup G)
    (n : ℕ) : (pCoreSeries p G n).comap H.subtype ≤ pCoreSeries p H n := by
  induction n with
  | zero =>
    rw [pCoreSeries_zero, pCoreSeries_zero]
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_bot] at hx
    rw [Subgroup.mem_bot]
    exact H.subtype_injective (by rw [hx, map_one])
  | succ n ih =>
    exact le_pCoreSeries_succ p H n (Subgroup.normal_comap H.subtype)
      (Subgroup.normal_comap H.subtype) (Subgroup.comap_mono (pCoreSeries_le_succ p G n))
      ih (subSeries_relIndex_isPiNat p G H n)

theorem isPSolvable_subgroup (p : ℕ) (G : Type*) [Group G] [Finite G] (H : Subgroup G)
    [Work.Fitting.IsPSolvable p G] : Work.Fitting.IsPSolvable p H := by
  obtain ⟨n, hn⟩ := (inferInstance : IsPSolvable p G).out
  refine ⟨n, ?_⟩
  have h := comap_pCoreSeries_le p G H n
  rw [hn, Subgroup.comap_top] at h
  exact top_le_iff.mp h

end Work.Fitting
