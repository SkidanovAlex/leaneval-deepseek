/-
Copyright: the martinet_totally_real_towers team.

# Exactness at `H¹(G,M)` of the restriction/inflation sequence

For a continuous open surjective homomorphism `q : G →* Q` of topological groups with
`N = ker q` (given by `i : N →* G` with `range i = ker q`), and a discrete `G`-module `M`
whose `G`-action is the pullback of a `Q`-action along `q` (`hcompQ`) and whose `N`-action is
the pullback along `i` (`hcompN`), the sequence

`H¹(Q,M) --H1Res q--> H¹(G,M) --H1Res i--> H¹(N,M)`

is exact at `H¹(G,M)`:

`H1Res i hi hcompN x = 0 ↔ ∃ y : H1 Q M, H1Res q hq hcompQ y = x`.

The inclusion `⊆` (the substance) is proved on the level of cochains.  If `z : Z¹(G,M)` has
restriction to `N` equal to a coboundary `d⁰m₀`, replace `z` by `fb = z - d⁰m₀`, so that
`fb ∘ i = 0`.  Two consequences of `fb ∘ i = 0` -- namely `fb` vanishes on `N`, and `i n • fb g = fb g`
for all `n ∈ N`, `g ∈ G` (from the normality of `ker q = range i`) -- show that `fb` is constant on
the fibres of `q`, so it descends to a function `F : Q → M` with `F ∘ q = fb`.  Normality gives the
crossed-homomorphism identity for `F`, openness of `q` gives local constancy of `F`, and then
`H1Res q [F] = [fb] = [z]`.

Note that the hypotheses force `N` to act trivially on `M` (via `hcompN` and `q ∘ i = 1`).
-/

import Mathlib
import Submission.Work.ConCohomology.Functoriality

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

/-! ### Auxiliary facts -/

/-- A crossed homomorphism (`1`-cocycle) takes the value `0` at `1`. -/
lemma isCocycle1_one {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    [DistribMulAction G M] {f : G → M} (hf : IsCocycle1 f) : f 1 = 0 := by
  have h := hf 1 1
  rw [mul_one, one_smul] at h
  exact add_left_cancel (a := f 1) (by rw [add_zero]; exact h.symm)

/-- `Z1Res` is given on cochains by pullback: its underlying `1`-cochain is `cochain1Res`. -/
lemma Z1Res_coe {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction H M]
    (ψ : H →* G) (hψ : Continuous ψ) (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m)
    [IsDiscreteGModule G M] [IsDiscreteGModule H M] (z : Z1 G M) :
    ((Z1Res ψ hψ hcomp z : Z1 H M) : Cochain1 H M) = cochain1Res ψ hψ (z : Cochain1 G M) :=
  rfl

/-- Evaluation of `Z1Res` on a `1`-cocycle. -/
@[simp] lemma Z1Res_apply {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction H M]
    (ψ : H →* G) (hψ : Continuous ψ) (hcomp : ∀ (h : H) (m : M), h • m = ψ h • m)
    [IsDiscreteGModule G M] [IsDiscreteGModule H M] (z : Z1 G M) (h : H) :
    (Z1Res ψ hψ hcomp z : H → M) h = (z : G → M) (ψ h) := by
  rw [Z1Res_coe, cochain1Res_apply]

/-! ### The main theorem -/

theorem ker_res_eq_range_inf {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    (q : G →* Q) (hq : Continuous q) (hsurj : Function.Surjective q) (hopen : IsOpenMap q)
    (i : N →* G) (hi : Continuous i)
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction Q M]
    [DistribMulAction N M] [IsDiscreteGModule G M] [IsDiscreteGModule Q M]
    [IsDiscreteGModule N M]
    (hcompQ : ∀ (g : G) (m : M), g • m = q g • m)
    (hcompN : ∀ (n : N) (m : M), n • m = i n • m)
    (hker : ∀ g : G, q g = 1 ↔ ∃ n : N, i n = g) (x : H1 G M) :
    H1Res i hi hcompN x = 0 ↔ ∃ y : H1 Q M, H1Res q hq hcompQ y = x := by
  have hqi : ∀ n : N, q (i n) = 1 := fun n => (hker (i n)).mpr ⟨n, rfl⟩
  constructor
  · -- `ker (H1Res i) ⊆ im (H1Res q)`: the substance
    intro hx
    revert hx
    refine QuotientAddGroup.induction_on x ?_
    intro z hz
    change H1Res i hi hcompN (H1.mk z) = 0 at hz
    change ∃ y : H1 Q M, H1Res q hq hcompQ y = H1.mk z
    -- the restriction of `z` to `N` is a coboundary `d⁰m₀`
    rw [H1Res_mk, H1.mk_eq_zero_iff, mem_B1', mem_B1] at hz
    obtain ⟨m0, hm0⟩ := hz
    have hzi : ∀ n : N, (z : Cochain1 G M) (i n) = i n • m0 - m0 := by
      intro n
      have h := DFunLike.congr_fun hm0 n
      rw [d0Hom_apply, Z1Res_coe, cochain1Res_apply] at h
      rw [hcompN n m0] at h
      exact h.symm
    -- the corrected cocycle, vanishing on `N`
    let fb : Cochain1 G M := (z : Cochain1 G M) - d0Hom G M m0
    have hfb_coc : IsCocycle1 (fb : G → M) := by
      intro σ τ
      have hz1 := mem_Z1.mp z.2 σ τ
      show (fb : G → M) (σ * τ) = (fb : G → M) σ + σ • (fb : G → M) τ
      simp only [fb, LocallyConstant.coe_sub, Pi.sub_apply, d0Hom_apply, smul_sub, mul_smul]
      rw [hz1]
      abel
    have hfb_zero : ∀ n : N, (fb : G → M) (i n) = 0 := by
      intro n
      have h1 : (fb : G → M) (i n) = (z : G → M) (i n) - (i n • m0 - m0) := by
        simp only [fb, LocallyConstant.coe_sub, Pi.sub_apply, d0Hom_apply]
      rw [h1, hzi n, sub_self]
    -- `range i = ker q` is normal in `G`, whence `fb` is `N`-invariant
    have hfb_inv : ∀ (n : N) (g : G), i n • (fb : G → M) g = (fb : G → M) g := by
      intro n g
      have hmem : q (g⁻¹ * i n * g) = 1 := by
        rw [map_mul, map_mul, map_inv, hqi n, mul_one, inv_mul_cancel]
      obtain ⟨n', hn'⟩ := (hker (g⁻¹ * i n * g)).mp hmem
      have hkey : i n * g = g * i n' := by rw [hn']; group
      have h1 : (fb : G → M) (i n * g) = i n • (fb : G → M) g := by
        rw [hfb_coc (i n) g, hfb_zero n, zero_add]
      have h2 : (fb : G → M) (i n * g) = (fb : G → M) g := by
        rw [hkey, hfb_coc g (i n'), hfb_zero n', smul_zero, add_zero]
      rw [← h1, h2]
    -- `fb` is constant on the fibres of `q`
    have hfb_factors : ∀ g g' : G, q g = q g' → (fb : G → M) g = (fb : G → M) g' := by
      intro g g' h
      have hmem : q (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
      obtain ⟨n, hn⟩ := (hker (g * g'⁻¹)).mp hmem
      have hkey : g = i n * g' := by rw [hn]; group
      rw [hkey, hfb_coc (i n) g', hfb_zero n, zero_add, hfb_inv n g']
    let F : Q → M := fun y => (fb : G → M) (Classical.choose (hsurj y))
    have hFq : ∀ g : G, F (q g) = (fb : G → M) g := fun g =>
      hfb_factors (Classical.choose (hsurj (q g))) g (Classical.choose_spec (hsurj (q g)))
    have hF_loc : IsLocallyConstant F := by
      rw [IsLocallyConstant.iff_exists_open]
      intro y
      obtain ⟨g, rfl⟩ := hsurj y
      obtain ⟨U, hU, hgU, hUc⟩ := (fb.isLocallyConstant).exists_open g
      refine ⟨q '' U, hopen U hU, ⟨g, hgU, rfl⟩, ?_⟩
      rintro y' ⟨g', hg'U, rfl⟩
      rw [hFq g', hFq g]
      exact hUc g' hg'U
    have hF_coc : IsCocycle1 F := by
      intro y y'
      obtain ⟨g, rfl⟩ := hsurj y
      obtain ⟨g', rfl⟩ := hsurj y'
      rw [← map_mul, hFq (g * g'), hFq g, hFq g', hfb_coc g g', hcompQ g ((fb : G → M) g')]
    let Fc : Z1 Q M := ⟨⟨F, hF_loc⟩, mem_Z1.mpr hF_coc⟩
    refine ⟨H1.mk Fc, ?_⟩
    rw [H1Res_mk, H1.mk_eq_mk_iff, mem_B1', mem_B1]
    refine ⟨-m0, ?_⟩
    ext g
    rw [d0Hom_apply, AddSubgroup.coe_sub, LocallyConstant.coe_sub, Pi.sub_apply,
      Z1Res_coe, cochain1Res_apply]
    show g • (-m0) - (-m0) = F (q g) - (z : G → M) g
    have hzfb : (fb : G → M) g = (z : G → M) g - (g • m0 - m0) := by
      simp only [fb, LocallyConstant.coe_sub, Pi.sub_apply, d0Hom_apply]
    rw [hFq g, hzfb, smul_neg]
    abel
  · -- `im (H1Res q) ⊆ ker (H1Res i)`: `H1Res (q ∘ i) = H1Res 1 = 0`
    rintro ⟨y, hy⟩
    rw [← hy]
    refine QuotientAddGroup.induction_on y ?_
    intro z
    change H1Res i hi hcompN (H1Res q hq hcompQ (H1.mk z)) = 0
    rw [H1Res_mk, H1Res_mk, H1.mk_eq_zero_iff, mem_B1', mem_B1]
    refine ⟨0, ?_⟩
    ext n
    rw [d0Hom_apply, smul_zero, sub_zero]
    rw [Z1Res_apply, Z1Res_apply, hqi n]
    exact (isCocycle1_one (mem_Z1.mp z.2)).symm

end Work.ConCohomology
