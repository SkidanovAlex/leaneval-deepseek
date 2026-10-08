/-
# `Work.NormalComplement.Sec5Fix.prop2c_kernel_P`

Peterfalvi I Ch. III §5, the fact used at the beginning of the proof of Prop. 2 (c) (p. 185):
`N_G(P)` acts on `Ω_P = fixedPts H P` (the set of points of `Ω = G ⧸ H` fixed by `P`), and the
kernel of this action is exactly `P`.  In the source this is used in the form "`N_G(P)/P` acts
2-transitively on `Ω_P`", which in particular says that the action is faithful modulo `P`.

The proof below does not need the 2-transitivity.  An element `x ∈ N_G(P)` fixing every point of
`Ω_P` lies in

  `K := N_G(P) ⊓ ⋂_{ω ∈ Ω_P} Stab_G(ω)`,

which is *normal in* `N_G(P)`; that is what makes §5 Lemma 1 (`Sec5Fix.lemma1`) applicable — the
subgroup `K`, contrary to a single element, is normalised by `N_H(P)`.  Concretely:

* `K ≤ H` and `K ≤ H^t`: the points `H` and `tH` of `Ω` lie in `Ω_P` because `P ≤ V = C_D(t)`,
  and the stabiliser of the coset `gH` is the conjugate `H^g = conj g H`;
* hence `K ≤ D ⊓ N_G(P) = (A ⊓ C_G(P)) ⊔ P ≤ V` (Ch. III §4 Lemma 1 (c), `sec4_one_c`);
* `P ≤ K` (`P` fixes its own fixed points) and `N_H(P) ≤ N_G(K)` (`K ⊴ N_G(P)`), so
  `Sec5Fix.lemma1` with `X = K` gives `K = P`, whence `x ∈ P`.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.NormalComplement.Sec5Fix.lemma1
import Submission.Work.ThreePoints.P3Sub.Helpers

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.Sec5Fix

variable {G : Type} [Group G] [Finite G]

/-! ## The kernel of the action of `N_G(P)` on `Ω_P = fixedPts H P` -/

/-- `K = N_G(P) ⊓ ⋂_{ω ∈ Ω_P} Stab_G(ω)`: the kernel of the action of `N_G(P)` on the set
`Ω_P = fixedPts H P` of points of `Ω = G ⧸ H` fixed by `P`.  (This is a subgroup of `G`, so
Lemma 1 of §5 can be applied to it; it is normal in `N_G(P)`.) -/
noncomputable def kernelNPAction (H P : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (P : Set G) ⊓
    ⨅ ω : ↥(Submission.Blueprint.fixedPts H P), MulAction.stabilizer G (ω : G ⧸ H)

/-- Membership in `kernelNPAction H P`. -/
theorem mem_kernelNPAction {H P : Subgroup G} {x : G} :
    x ∈ kernelNPAction H P ↔ x ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ ω : G ⧸ H, ω ∈ Submission.Blueprint.fixedPts H P → x • ω = ω := by
  rw [kernelNPAction, Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ω hω => MulAction.mem_stabilizer_iff.mp (h2 ⟨ω, hω⟩)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ω => MulAction.mem_stabilizer_iff.mpr (h2 ω ω.2)⟩

/-- `N_G(P)` permutes `Ω_P = fixedPts H P`: if `ω` is fixed by `P` and `n` normalises `P`, then
`n • ω` is fixed by `P`. -/
theorem smul_mem_fixedPts_of_mem_normalizer {H X : Subgroup G} {ω : G ⧸ H}
    (hω : ω ∈ Submission.Blueprint.fixedPts H X) {n : G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) :
    n • ω ∈ Submission.Blueprint.fixedPts H X := by
  rw [Work.ThreePoints.mem_fixedPts] at hω ⊢
  intro x hx
  have hxn : n⁻¹ * x * n ∈ X := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp hx
    rwa [inv_inv] at h
  calc x • (n • ω) = (x * n) • ω := (mul_smul x n ω).symm
    _ = (n * (n⁻¹ * x * n)) • ω := by rw [show x * n = n * (n⁻¹ * x * n) from by group]
    _ = n • ((n⁻¹ * x * n) • ω) := mul_smul n _ ω
    _ = n • ω := by rw [hω _ hxn]

/-- Conjugation by an element of `N_G(P)` preserves the kernel `kernelNPAction H P`. -/
theorem conj_mem_kernelNPAction {H P : Subgroup G} {g y : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hy : y ∈ kernelNPAction H P) :
    g * y * g⁻¹ ∈ kernelNPAction H P := by
  obtain ⟨hyN, hyfix⟩ := mem_kernelNPAction.mp hy
  have hg' : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem hg
  refine mem_kernelNPAction.mpr ⟨?_, ?_⟩
  · exact (Subgroup.normalizer (P : Set G)).mul_mem
      ((Subgroup.normalizer (P : Set G)).mul_mem hg hyN) hg'
  · intro ω hω
    have hmem := smul_mem_fixedPts_of_mem_normalizer (X := P) hω hg'
    calc (g * y * g⁻¹) • ω = g • (y • (g⁻¹ • ω)) := by rw [mul_smul, mul_smul]
      _ = g • (g⁻¹ • ω) := by rw [hyfix _ hmem]
      _ = ω := smul_inv_smul g ω

/-- `kernelNPAction H P` is normal in `N_G(P)`. -/
theorem normalizer_le_normalizer_kernelNPAction (H P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (kernelNPAction H P : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy; exact conj_mem_kernelNPAction hg hy
  · intro hy
    have h := conj_mem_kernelNPAction (H := H) (P := P)
      ((Subgroup.normalizer (P : Set G)).inv_mem hg) hy
    have h2 : g⁻¹ * (g * y * g⁻¹) * (g⁻¹)⁻¹ = y := by group
    rwa [h2] at h

/-- `P` is contained in the kernel: every element of `P` fixes `Ω_P` pointwise. -/
theorem le_kernelNPAction {H P : Subgroup G} : P ≤ kernelNPAction H P := by
  intro p hp
  refine mem_kernelNPAction.mpr ⟨Subgroup.le_normalizer hp, ?_⟩
  intro ω hω
  exact hω p hp

/-! ## The kernel is contained in `V = C_D(t)` -/

/-- `kernelNPAction H P ≤ H`: the point `H = mk 1` is fixed by `P` (as `P ≤ V ≤ H`) and has
stabiliser `H`. -/
theorem kernelNPAction_le_H {H P : Subgroup G} {t : G}
    (hPleV : P ≤ Submission.Blueprint.centD H t) : kernelNPAction H P ≤ H := by
  intro k hk
  have hfix := (mem_kernelNPAction.mp hk).2 _
    (Work.ThreePoints.pt_mem_fixedPts_of_le_centD hPleV)
  have h1 : ((k * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by simpa using hfix
  have h2 : (k * 1)⁻¹ * 1 ∈ H := QuotientGroup.eq.mp h1
  simpa using H.inv_mem h2

/-- `kernelNPAction H P ≤ H^t`: the point `tH` is fixed by `P` (as `P ≤ V ≤ H^t`) and has
stabiliser `H^t = conj t H`. -/
theorem kernelNPAction_le_conj_t {H P : Subgroup G} {t : G}
    (hPleV : P ≤ Submission.Blueprint.centD H t) :
    kernelNPAction H P ≤ Submission.Blueprint.conj t H := by
  intro k hk
  have hfix := (mem_kernelNPAction.mp hk).2 _
    (Work.ThreePoints.mk_t_mem_fixedPts_of_le_centD hPleV)
  have h1 : ((k * t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by simpa using hfix
  have h2 : (k * t)⁻¹ * t ∈ H := QuotientGroup.eq.mp h1
  have h3 : t⁻¹ * k⁻¹ * t ∈ H := by simpa using h2
  have h4 : k⁻¹ ∈ Submission.Blueprint.conj t H := by
    rw [Submission.Blueprint.conj, Subgroup.mem_map]
    refine ⟨t⁻¹ * k⁻¹ * t, h3, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  simpa using (Submission.Blueprint.conj t H).inv_mem h4

/-- `kernelNPAction H P ≤ D ⊓ N_G(P) = (A ⊓ C_G(P)) ⊔ P ≤ V`: the kernel fixes `H` and `tH`, so
it lies in `D`, and it normalises `P` by definition; Ch. III §4 Lemma 1 (c) (`sec4_one_c`)
identifies `D ⊓ N_G(P)`, and both `A ≤ V` and `P ≤ V`. -/
theorem kernelNPAction_le_centD (hFT : Submission.Blueprint.FeitThompsonProp)
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Design.Setup5 G H t W p P A r) :
    kernelNPAction H P ≤ Submission.Blueprint.centD H t := by
  have hPleV : P ≤ Submission.Blueprint.centD H t := h.P_le.trans inf_le_right
  have hD : Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (P : Set G) =
      (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P :=
    (Work.NormalComplement.sec4_one_c hFT h.toSetup45A).1
  intro k hk
  have hkD : k ∈ Submission.Blueprint.twoPoint H t :=
    le_inf (kernelNPAction_le_H hPleV) (kernelNPAction_le_conj_t hPleV) hk
  have hkN : k ∈ Subgroup.normalizer (P : Set G) := (mem_kernelNPAction.mp hk).1
  have hk' : k ∈ (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P := by
    rw [← hD]; exact ⟨hkD, hkN⟩
  exact (sup_le (le_trans inf_le_left h.A_le) hPleV) hk'

/-! ## §5 Prop. 2 (c): the kernel is `P` -/

theorem prop2c_kernel_P (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G)) :
    ∀ x ∈ Subgroup.normalizer (P : Set G),
      (∀ ω ∈ Submission.Blueprint.fixedPts H P, x • ω = ω) → x ∈ P := by
  intro x hxN hxfix
  have hxK : x ∈ kernelNPAction H P := mem_kernelNPAction.mpr ⟨hxN, hxfix⟩
  have hKleV : kernelNPAction H P ≤ Submission.Blueprint.centD H t :=
    kernelNPAction_le_centD hFT h
  have hN : H ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (kernelNPAction H P : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_kernelNPAction H P)
  have hKP : kernelNPAction H P = P :=
    lemma1 hFT hP3 h (kernelNPAction H P) le_kernelNPAction hKleV hN
  rwa [hKP] at hxK

end Work.NormalComplement.Sec5Fix
