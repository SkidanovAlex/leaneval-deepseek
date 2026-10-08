import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.isPSolvable_subgroup
import Submission.Work.Fitting.isPSolvable_quotient
import Submission.Work.Fitting.pLength_quotient_le
import Submission.Work.Fitting.pLength_spec
import Submission.Work.Fitting.pLength_le_iff
import Submission.Work.Fitting.pCoreSeries_one
import Submission.Work.Fitting.pCoreSeries_mono
import Submission.Work.Fitting.piCore_quotient_eq_bot
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.pLength_quotient_pPrimeCore`

The `p`-length of `G` is unchanged on passing to `G ⧸ O_{p'}(G)`:

`ℓ_p(G ⧸ O_{p'}(G)) = ℓ_p(G)`.

The upper `p`-series of `G` starts `1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ ...`; the first step is a
`p'`-step and hence contributes no `p`-factor.  Concretely, writing `π : G → G/O_{p'}(G)`
for the quotient map (`O = O_{p'}(G) = ker π`), the two series are related by

`(pCoreSeries p (G ⧸ O) n).comap π = pCoreSeries p G n`  for all `n ≥ 1`,

so `G` reaches the top at index `n ≥ 1` exactly when `G ⧸ O` does.  Since `pLength` is half
the least such index — and index `0` is the top only for the trivial group — the `p`-lengths
coincide.
-/

set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.Fitting

variable {G : Type*} [Group G] [Finite G]

/-- **One half of the series comparison.**  Every term of the upper `p`-series of `G` maps
into the corresponding term of the upper `p`-series of `G ⧸ O_{p'}(G)`; equivalently the
`n`-th term of the former is contained in the preimage of the `n`-th term of the latter. -/
theorem pCoreSeries_quotient_comap_le (p : ℕ) (G : Type*) [Group G] [Finite G] (n : ℕ) :
    pCoreSeries p G n ≤ (pCoreSeries p (G ⧸ pPrimeCore p G) n).comap
      (QuotientGroup.mk' (pPrimeCore p G)) := by
  haveI : Finite (G ⧸ pPrimeCore p G) :=
    (finite_iff_subgroup_quotient (pPrimeCore p G)).mp ‹Finite G› |>.2
  calc pCoreSeries p G n
      ≤ (Subgroup.map (QuotientGroup.mk' (pPrimeCore p G)) (pCoreSeries p G n)).comap
          (QuotientGroup.mk' (pPrimeCore p G)) := Subgroup.le_comap_map _ _
    _ ≤ (pCoreSeries p (G ⧸ pPrimeCore p G) n).comap
          (QuotientGroup.mk' (pPrimeCore p G)) :=
        Subgroup.comap_mono (pCoreSeries_map_le p G (G ⧸ pPrimeCore p G)
          (QuotientGroup.mk' (pPrimeCore p G))
          (QuotientGroup.mk'_surjective (pPrimeCore p G)) n)

/-- **The other half of the series comparison, with the shift.**  For every `n`, the preimage
of the `(n+1)`-st term of the upper `p`-series of `G ⧸ O_{p'}(G)` under the quotient map is
contained in the `(n+1)`-st term of the upper `p`-series of `G`.

The induction runs on `n` (the base case `n = 0` uses `O_{p'}(G/O_{p'}(G)) = 1`): writing
`Q_m` for the upper `p`-series of `Q = G ⧸ O_{p'}(G)`, the preimage of `Q_{n+1}` is the kernel
of `ρ : G → Q ⧸ Q_{n+1}`, while the preimage of `Q_{n+2}` is the preimage under `ρ` of the
`π`-core of `Q ⧸ Q_{n+1}`; the subquotient is therefore a `p'`-group (`n+1` even) or a
`p`-group (`n+1` odd), which is what `le_pCoreSeries_succ` needs. -/
theorem pCoreSeries_quotient_comap_ge (p : ℕ) (G : Type*) [Group G] [Finite G] :
    ∀ n : ℕ, (pCoreSeries p (G ⧸ pPrimeCore p G) (n + 1)).comap
        (QuotientGroup.mk' (pPrimeCore p G)) ≤ pCoreSeries p G (n + 1) := by
  haveI hQfin : Finite (G ⧸ pPrimeCore p G) :=
    (finite_iff_subgroup_quotient (pPrimeCore p G)).mp ‹Finite G› |>.2
  intro n
  induction n with
  | zero =>
      have hQ1 : pCoreSeries p (G ⧸ pPrimeCore p G) 1 = ⊥ := by
        rw [pCoreSeries_one]
        change piCore (fun q => q ≠ p) (G ⧸ piCore (fun q => q ≠ p) G) = ⊥
        exact piCore_quotient_eq_bot (fun q => q ≠ p) G
      rw [Nat.zero_add, hQ1, MonoidHom.comap_bot, QuotientGroup.ker_mk', pCoreSeries_one]
  | succ n ih =>
      let Qn : Subgroup (G ⧸ pPrimeCore p G) := pCoreSeries p (G ⧸ pPrimeCore p G) (n + 1)
      haveI hQnN : Qn.Normal := pCoreSeries_normal p (G ⧸ pPrimeCore p G) (n + 1)
      let Rn : Subgroup ((G ⧸ pPrimeCore p G) ⧸ Qn) :=
        piCore (stepPi p (n + 1)) ((G ⧸ pPrimeCore p G) ⧸ Qn)
      let rho : G →* ((G ⧸ pPrimeCore p G) ⧸ Qn) :=
        (QuotientGroup.mk' Qn).comp (QuotientGroup.mk' (pPrimeCore p G))
      have hrho : Function.Surjective rho :=
        (QuotientGroup.mk'_surjective Qn).comp
          (QuotientGroup.mk'_surjective (pPrimeCore p G))
      -- `rho.ker` is the preimage of the `(n+1)`-st term
      have hker : rho.ker = (pCoreSeries p (G ⧸ pPrimeCore p G) (n + 1)).comap
          (QuotientGroup.mk' (pPrimeCore p G)) := by
        rw [show rho = (QuotientGroup.mk' Qn).comp (QuotientGroup.mk' (pPrimeCore p G))
              from rfl, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      -- the preimage of the `(n+2)`-nd term is `comap rho R`
      have hcomap : (pCoreSeries p (G ⧸ pPrimeCore p G) ((n + 1) + 1)).comap
            (QuotientGroup.mk' (pPrimeCore p G)) = Subgroup.comap rho Rn := by
        have hQ2 : pCoreSeries p (G ⧸ pPrimeCore p G) ((n + 1) + 1) =
            Subgroup.comap (QuotientGroup.mk' Qn) Rn := by
          rw [pCoreSeries_succ]
          rfl
        rw [show rho = (QuotientGroup.mk' Qn).comp (QuotientGroup.mk' (pPrimeCore p G))
              from rfl, hQ2, Subgroup.comap_comap]
      -- the subquotient is a `p'`- or `p`-number
      have hcard : IsPiNat (stepPi p (n + 1))
          (((pCoreSeries p (G ⧸ pPrimeCore p G) (n + 1)).comap
              (QuotientGroup.mk' (pPrimeCore p G))).relIndex
            ((pCoreSeries p (G ⧸ pPrimeCore p G) ((n + 1) + 1)).comap
              (QuotientGroup.mk' (pPrimeCore p G)))) := by
        rw [← hker, hcomap, Subgroup.relIndex_ker]
        rw [Subgroup.map_comap_eq_self (by
          rw [MonoidHom.range_eq_top.mpr hrho]; exact le_top)]
        haveI : Finite ((G ⧸ pPrimeCore p G) ⧸ Qn) :=
          Finite.of_surjective (QuotientGroup.mk' Qn) (QuotientGroup.mk'_surjective Qn)
        exact piCore_isPiNat ((G ⧸ pPrimeCore p G) ⧸ Qn) (stepPi p (n + 1))
      have hNM : (pCoreSeries p (G ⧸ pPrimeCore p G) (n + 1)).comap
            (QuotientGroup.mk' (pPrimeCore p G)) ≤
          (pCoreSeries p (G ⧸ pPrimeCore p G) ((n + 1) + 1)).comap
            (QuotientGroup.mk' (pPrimeCore p G)) :=
        Subgroup.comap_mono (pCoreSeries_le_succ p (G ⧸ pPrimeCore p G) (n + 1))
      exact le_pCoreSeries_succ p G (n + 1) (Subgroup.normal_comap _)
        (Subgroup.normal_comap _) hNM ih hcard

/-- The two upper `p`-series agree after pulling back along `G → G ⧸ O_{p'}(G)`, at every
index `n ≥ 1`. -/
theorem pCoreSeries_quotient_comap (p : ℕ) (G : Type*) [Group G] [Finite G] (m : ℕ) :
    (pCoreSeries p (G ⧸ pPrimeCore p G) (m + 1)).comap (QuotientGroup.mk' (pPrimeCore p G)) =
      pCoreSeries p G (m + 1) :=
  le_antisymm (pCoreSeries_quotient_comap_ge p G m) (pCoreSeries_quotient_comap_le p G _)

/-- **The `p`-length is unchanged on factoring out the `p'`-core.**
`ℓ_p(G ⧸ O_{p'}(G)) = ℓ_p(G)`: the `p'`-step `1 ≤ O_{p'}(G)` at the bottom of the upper
`p`-series of `G` contributes no `p`-factor, and the two series are otherwise identified by
`pCoreSeries_quotient_comap`. -/
theorem pLength_quotient_pPrimeCore (p : ℕ) (hp : p.Prime) (G : Type*) [Group G] [Finite G]
    [Work.Fitting.IsPSolvable p G] :
    Work.Fitting.pLength p (G ⧸ Work.Fitting.pPrimeCore p G) = Work.Fitting.pLength p G := by
  have _ := hp
  haveI hQfin : Finite (G ⧸ pPrimeCore p G) :=
    (finite_iff_subgroup_quotient (pPrimeCore p G)).mp ‹Finite G› |>.2
  haveI hQsol : IsPSolvable p (G ⧸ pPrimeCore p G) :=
    isPSolvable_quotient p G (pPrimeCore p G)
  refine le_antisymm (pLength_quotient_le p G (pPrimeCore p G)) ?_
  rw [pLength_le_iff p G (inferInstance) (pLength p (G ⧸ pPrimeCore p G))]
  have hspec : pCoreSeries p (G ⧸ pPrimeCore p G) (2 * pLength p (G ⧸ pPrimeCore p G) + 1) =
      ⊤ := pLength_spec p (G ⧸ pPrimeCore p G) (inferInstance)
  rw [← pCoreSeries_quotient_comap p G (2 * pLength p (G ⧸ pPrimeCore p G)), hspec,
    Subgroup.comap_top]

end Work.Fitting
