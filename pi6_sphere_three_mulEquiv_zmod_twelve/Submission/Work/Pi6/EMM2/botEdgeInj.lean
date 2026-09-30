import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Pi6.EMM2.SSKit
import Submission.Work.Pi6.EMM2.K2F9Kit
import Submission.Work.Pi6.EMM2.K4Kit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# Injectivity of the bottom edge of the Serre spectral sequence in degree `2`

`p^* : H²(B;𝕜) → H²(E;𝕜)` is the first stage of the edge map of the Serre spectral sequence,
`H²(B;𝕜) = E_2^{2,0} → E_∞^{2,0} ↪ H²(E;𝕜)`.  Its kernel is the image of the transgression
`d_2 : E_2^{0,1} → E_2^{2,0}`, so it vanishes as soon as `H¹(F) = 0`.

In the formalisation of the interface `Work.Pi6.IsSerreMSS` the edge map is recorded as

`(S.botTo 2 2).hom (e₂⁻¹ (b ⊗ 1)) = 0 ↔ (cmap 𝕜 p 2).hom b = 0`   (`hedge`),

so it remains to see that `S.botTo 2 2 : E_2^{2,0} → E_4^{2,0}` is injective.  Its two factors are
the quotient maps `E_2^{2,0} → E_3^{2,0}` and `E_3^{2,0} → E_4^{2,0}`, whose kernels are the images
of the incoming differentials `E_2^{0,1} → E_2^{2,0}` and `E_3^{-1,2} → E_3^{2,0}`; the second
source is in a negative bidegree and the first vanishes because `H¹(F) = 0`.  Finally
`b ⊗ 1 ≠ 0` for `b ≠ 0` because `H⁰(F) = 𝕜 · 1` is one-dimensional (`hF0`, `hFinF`) and the unit of
the cup ring is nonzero (`hco`).

Everything is proved for `N = 3`, the range in which the edge map is available.
-/

namespace Work.Pi6.EMM2

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝕜 : Type} [Field 𝕜]

/-- The row-`0` quotient map `E_r^{s,0} → E_{r+1}^{s,0}` is injective when the incoming
differential at `(s,0)` vanishes. -/
theorem bot_injective (S : CohSS 𝕜) (r : ℕ) (hr : 2 ≤ r) (s : ℤ)
    (hzero : IsZero (S.E r ((s, 0) - vr r))) :
    Function.Injective (S.bot r s).hom := by
  -- every class in the row `0` is a cycle: the target of the differential is in a negative bidegree
  have hcyc : ∀ z : S.E r (s, 0), (S.d r (s, 0) ((s, 0) + vr r)).hom z = 0 := by
    intro z
    have h : S.d r (s, 0) ((s, 0) + vr r) = 0 :=
      S.d_eq_zero_of_isZero (S.quad r ((s, 0) + vr r) (Or.inr (by simp [vr]; omega)))
    rw [h, ModuleCat.hom_zero, LinearMap.zero_apply]
  have hd : S.d r ((s, 0) - vr r) (s, 0) = 0 := hzero.eq_of_src _ _
  have key : ∀ z : S.E r (s, 0), (S.bot r s).hom z = 0 → z = 0 := by
    intro z hz
    have h1 : S.proj r (s, 0)
        (⟨z, hcyc z⟩ : ↥(LinearMap.ker (S.d r (s, 0) ((s, 0) + vr r)).hom)) = 0 := by
      rw [← S.bot_spec r s ⟨z, hcyc z⟩ hr]
      exact hz
    have h2 : z ∈ LinearMap.range (S.d r ((s, 0) - vr r) (s, 0)).hom :=
      (S.proj_ker r (s, 0) hr ⟨z, hcyc z⟩).mp h1
    rw [hd, ModuleCat.hom_zero, LinearMap.range_zero, Submodule.mem_bot] at h2
    exact h2
  intro x y hxy
  have hsub : (S.bot r s).hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key (x - y) hsub)

/-- The iterated bottom-row map `E_2^{s,0} → E_{k+2}^{s,0}` is injective as soon as all the
intermediate quotient maps are. -/
theorem botTo_injective (S : CohSS 𝕜) (s : ℤ) (k : ℕ)
    (h : ∀ r : ℕ, 2 ≤ r → r ≤ k + 1 → Function.Injective (S.bot r s).hom) :
    Function.Injective (S.botTo s k).hom := by
  induction k with
  | zero => intro x y hxy; exact hxy
  | succ k ih =>
      have hk : ∀ r : ℕ, 2 ≤ r → r ≤ k + 1 → Function.Injective (S.bot r s).hom :=
        fun r h2 h3 => h r h2 (by omega)
      have hb : Function.Injective (S.bot (k + 2) s).hom := h (k + 2) (by omega) (by omega)
      have hcomp : ∀ z : S.E 2 (s, 0),
          (S.botTo s (k + 1)).hom z = (S.bot (k + 2) s).hom ((S.botTo s k).hom z) := by
        intro z
        rw [show S.botTo s (k + 1) = S.botTo s k ≫ S.bot (k + 2) s from rfl,
          ModuleCat.hom_comp, LinearMap.comp_apply]
      intro x y hxy
      exact ih hk (hb (by simpa only [hcomp] using hxy))

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The bottom edge of the Serre spectral sequence is injective in degree `2`.**

If `p : E → B` has a Serre spectral sequence over `𝕜` through total degree `3` whose fibre
`F = fiber p (p e₀)` has `H⁰(F) = 𝕜` (one-dimensional), `H¹(F) = 0`, `H⁰(F)` finite dimensional, then
`p^* : H²(B;𝕜) → H²(E;𝕜)` is injective. -/
theorem botEdgeInj
    {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (S : Work.Pi6.CohSS 𝕜) (hS : Work.Pi6.IsSerreMSS S p e₀ 3)
    (hF0 : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0) = 1)
    (hF1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 1))
    (hFinF : FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0))
    (hco : Work.Pi6.EMM2.CupOneStatement) :
    Function.Injective (Work.Pi6.cmap 𝕜 p 2) := by
  -- the unit of the cup ring of the fibre is nonzero
  have hone : one 𝕜 (Work.StemsB.fibre p (p e₀)) ≠ 0 := K2F9.one_ne_zero hco hF0 hFinF
  -- the whole column `q = 1` of the `E_2`-page vanishes
  have hE01 : IsZero (S.E 2 ((0 : ℤ), (1 : ℤ))) :=
    k4_isZero_E2_right p e₀ S 3 hS (s := 0) (q := 1) (by omega) (by omega) hF1
  obtain ⟨e2, _hmul, _hvan, _hconv, hedge, _hcol⟩ := hS
  -- the two quotient maps of the bottom row at `(2,0)` are injective
  have hbot2 : Function.Injective (S.bot 2 (2 : ℤ)).hom := by
    refine bot_injective S 2 (by norm_num) 2 ?_
    have h : (((2 : ℤ), (0 : ℤ)) - vr 2) = ((0 : ℤ), (1 : ℤ)) := by ext <;> simp [vr]
    rw [h]; exact hE01
  have hbot3 : Function.Injective (S.bot 3 (2 : ℤ)).hom := by
    refine bot_injective S 3 (by norm_num) 2 ?_
    have hq : IsZero (S.E 3 (((-1 : ℤ), (2 : ℤ)))) :=
      S.quad 3 (((-1 : ℤ), (2 : ℤ))) (Or.inl (by simp))
    have h : (((2 : ℤ), (0 : ℤ)) - vr 3) = ((-1 : ℤ), (2 : ℤ)) := by ext <;> simp [vr]
    rw [h]; exact hq
  have hbotTo : Function.Injective (S.botTo (2 : ℤ) 2).hom :=
    botTo_injective S (2 : ℤ) 2 (by
      intro r h2 h3
      interval_cases r
      · exact hbot2
      · exact hbot3)
  -- hence `b ≠ 0` for `b` in the kernel of the edge map
  have key : ∀ b : Coh 𝕜 B 2, (cmap 𝕜 p 2).hom b = 0 → b = 0 := by
    intro b hb
    have main : ∀ (hs : (2 : ℕ) ≤ 3) (hq : (0 : ℕ) ≤ 3),
        (S.botTo ((2 : ℕ) : ℤ) 2).hom
          ((e2 2 0 hs hq).inv.hom (b ⊗ₜ[𝕜] one 𝕜 (Work.StemsB.fibre p (p e₀)))) = 0 →
        b = 0 := by
      intro hs hq hx0
      have hx : (e2 2 0 hs hq).inv.hom
          (b ⊗ₜ[𝕜] one 𝕜 (Work.StemsB.fibre p (p e₀))) = 0 := by
        refine hbotTo ?_
        show (S.botTo ((2 : ℕ) : ℤ) 2).hom
              ((e2 2 0 hs hq).inv.hom
                (b ⊗ₜ[𝕜] one 𝕜 (Work.StemsB.fibre p (p e₀)))) =
            (S.botTo ((2 : ℕ) : ℤ) 2).hom 0
        rw [hx0, map_zero]
      have hb1 : b ⊗ₜ[𝕜] one 𝕜 (Work.StemsB.fibre p (p e₀)) = 0 := by
        have h := k4_iso_hom_inv_hom_apply (e2 2 0 hs hq)
          (b ⊗ₜ[𝕜] one 𝕜 (Work.StemsB.fibre p (p e₀)))
        rw [← h, hx, map_zero]
      exact K2F9.eq_zero_of_tmul_eq_zero (one 𝕜 (Work.StemsB.fibre p (p e₀))) hone b hb1
    exact main _ _ ((hedge 2 (by omega) b).mpr hb)
  intro a b hab
  have hsub : (cmap 𝕜 p 2).hom (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key (a - b) hsub)

end

end Work.Pi6.EMM2
