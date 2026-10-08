import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.Case2LayerOneInvClass

-- the bundle `I` is part of the requested signature but is not used by this step of §4
set_option linter.unusedVariables false

open Work.GW2

namespace Work.CORE4

open Subgroup

/-! ## Conjugation toolkit for `Work.GW2.conjSub`

`conjSub g K = g K g⁻¹`.  These four facts are the ones Bender's argument uses; they are proved
here so that this file is self-contained (the same statements are also being contributed to the
shared library under `Submission/Work/CORE4/ConjSub/`). -/

/-- `x ↦ g x g⁻¹` preserves orders. -/
private lemma orderOf_conj_mul {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply g x]
  exact (MulAut.conj g).orderOf_eq x

/-- `x ∈ K^g ↔ g⁻¹ x g ∈ K`. -/
private lemma mem_conjSub_iff' {G : Type*} [Group G] {g x : G} {K : Subgroup G} :
    x ∈ Work.GW2.conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  rw [Work.GW2.conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, hmx⟩
    have hmx' : g * m * g⁻¹ = x := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmx
    rwa [← hmx', show g⁻¹ * (g * m * g⁻¹) * g = m from by group]
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

/-- `g x g⁻¹ ∈ K^g` for `x ∈ K`. -/
private lemma conj_mem_conjSub' {G : Type*} [Group G] {g x : G} {K : Subgroup G}
    (hx : x ∈ K) : g * x * g⁻¹ ∈ Work.GW2.conjSub g K := by
  rw [mem_conjSub_iff']
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x from by group]

/-- **Conjugation of subgroups is a right action:** `(K^h)^g = K^{gh}`. -/
private lemma conjSub_mul' {G : Type*} [Group G] (g h : G) (K : Subgroup G) :
    Work.GW2.conjSub (g * h) K = Work.GW2.conjSub g (Work.GW2.conjSub h K) := by
  rw [Work.GW2.conjSub, Work.GW2.conjSub, Work.GW2.conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

/-- **The normalizer of a conjugate subgroup:** `N_G(K^g) = (N_G K)^g`. -/
private lemma normalizer_conjSub' {G : Type*} [Group G] (g : G) (K : Subgroup G) :
    Subgroup.normalizer ((Work.GW2.conjSub g K : Subgroup G) : Set G) =
      Work.GW2.conjSub g (Subgroup.normalizer (K : Set G)) :=
  (Subgroup.map_equiv_normalizer_eq K (MulAut.conj g)).symm

/-- **`OneInvClassIn` is preserved by conjugation.**  If the involutions of `K` form a single
`K`-conjugacy class, the same holds for `K^g = g K g⁻¹` under conjugation by its own elements. -/
private lemma oneInvClassIn_conjSub' {G : Type*} [Group G] {K : Subgroup G}
    (h : Work.GW2.OneInvClassIn K) (g : G) :
    Work.GW2.OneInvClassIn (Work.GW2.conjSub g K) := by
  intro x hx y hy
  rw [Work.GW2.involutionSet, Set.mem_ofPred_eq] at hx hy
  obtain ⟨hxK, hx2⟩ := hx
  obtain ⟨hyK, hy2⟩ := hy
  have hxK' : g⁻¹ * x * g ∈ K := mem_conjSub_iff'.mp hxK
  have hyK' : g⁻¹ * y * g ∈ K := mem_conjSub_iff'.mp hyK
  have hx2' : orderOf (g⁻¹ * x * g) = 2 := by
    have h := orderOf_conj_mul (g := g⁻¹) x
    rwa [inv_inv, hx2] at h
  have hy2' : orderOf (g⁻¹ * y * g) = 2 := by
    have h := orderOf_conj_mul (g := g⁻¹) y
    rwa [inv_inv, hy2] at h
  obtain ⟨n, hnK, hn⟩ := h (g⁻¹ * x * g) ⟨hxK', hx2'⟩ (g⁻¹ * y * g) ⟨hyK', hy2'⟩
  refine ⟨g * n * g⁻¹, conj_mem_conjSub' hnK, ?_⟩
  have hkey : (g * n * g⁻¹) * x * (g * n * g⁻¹)⁻¹ =
      g * (n * (g⁻¹ * x * g) * n⁻¹) * g⁻¹ := by group
  rw [hkey, hn]
  group

/-- **Bender 1981, §4, p. 227, the choice of `g` with `t^g = t`.**

Bender, verbatim: *"Fix such a conjugate `X`, say `X = P^g ≤ A`.  As `N_G(X) = M^g` has only one
class of involutions, we can choose `g` subject to `t^g = t`."*

Formalised (with the involution-class input made explicit as a hypothesis, since it is *proved*
separately from `Case2Ctx` by `Work.CORE4.OneInvClassM` — it is **not** among `Case2Ctx`'s
conjuncts): for the §4 configuration `h : Case2Ctx B`, the odd prime `p` of §4 (8), Bender's
`(p,p)`-subgroup `A` of `F ⊔ K` containing `P ≤ F` of order `p`, and every conjugate `X ≤ A`
(`X ≠ P`, `X ~ P`) of `P` inside `A`, there is `h' ∈ B.H = C_G(t)` with `conjSub h' P = X`.

## Route (checked by the reviewer)

1. `A ≤ B.U ≤ B.H`: `A ≤ D.F ⊔ D.K` with `D.F ≤ D.B0 = (U⊓M) ⊓ C_G(s) ≤ U` and
   `D.K ≤ U ⊓ M ≤ U`; hence `t` centralizes `A`, so `t ∈ C_G(X) ≤ N_G(X) = M^g`
   (`Work.CORE4.Case2NormalizerP`: `N_G(P^g) = M^g`).
2. `t^g = g t g⁻¹ ∈ M^g` is an involution (because `t ∈ M`, `D.t_mem`), and
   `OneInvClassIn h.D.M` transported along `MulAut.conj g` gives `OneInvClassIn (M^g)`, so there
   is `n ∈ M^g` with `n (g t g⁻¹) n⁻¹ = t`.
3. `h' := n * g` then has `conjSub (n*g) P = conjSub n (conjSub g P) = X` (as `n ∈ N_G(X)`) and
   `(n*g) * t * (n*g)⁻¹ = t`, i.e. `h' ∈ B.H`. -/
theorem ConjInAH (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        OneInvClassIn h.D.M →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
          Work.GW2.Case2EightObj h.D p P A →
          ∀ X : Subgroup G, X ≤ A → X ≠ P → (∃ g : G, X = Work.GW2.conjSub g P) →
            ∃ h' ∈ B.H, Work.GW2.conjSub h' P = X := by
  intro G _ _ _ B h hone p P A hp hPF hPcard hObj X hXA _ hconj
  obtain ⟨g, hg⟩ := hconj
  -- `P` is nontrivial, of prime order `p`
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    exact hp.ne_one hPcard.symm
  -- §4 (11): `N_G(P) = M`, hence `N_G(X) = N_G(P^g) = M^g`
  have hNP : Subgroup.normalizer (P : Set G) = h.D.M := Case2NormalizerP G B h P hPF hPne
  have hNX : Subgroup.normalizer (X : Set G) = Work.GW2.conjSub g h.D.M := by
    rw [hg, normalizer_conjSub', hNP]
  -- `A ≤ D.F ⊔ D.K ≤ U ≤ H = C_G(t)`, so `t` centralises `A` and hence `X`
  have hAUK : A ≤ h.D.F ⊔ h.D.K := hObj.2.2.2.1
  have hAU : A ≤ B.U :=
    le_trans hAUK (sup_le (Case2Data.F_le_U B h.D) (Case2Data.K_le_U B h.D))
  have htCenA : B.t ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (BenderSetup.U_le_H B (hAU ha))
  have htNX : B.t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G)
      (Subgroup.centralizer_le (s := (X : Set G)) (t := (A : Set G)) hXA htCenA)
  -- `t ∈ M^g`; and `t ∈ M`, whence `t^g = g t g⁻¹ ∈ M^g` as well
  have htMg : B.t ∈ Work.GW2.conjSub g h.D.M := hNX ▸ htNX
  have htM : B.t ∈ h.D.M := layerIn_le h.D.M h.D.t_mem
  have hgtMg : g * B.t * g⁻¹ ∈ Work.GW2.conjSub g h.D.M := conj_mem_conjSub' htM
  have htInv : B.t ∈ Work.GW2.involutionSet (Work.GW2.conjSub g h.D.M) := ⟨htMg, B.t_order⟩
  have hgtInv : g * B.t * g⁻¹ ∈ Work.GW2.involutionSet (Work.GW2.conjSub g h.D.M) :=
    ⟨hgtMg, by rw [orderOf_conj_mul, B.t_order]⟩
  -- `M^g` has one class of involutions: pick `n ∈ M^g` with `n (g t g⁻¹) n⁻¹ = t`
  obtain ⟨n, hnMg, hnconj⟩ :=
    oneInvClassIn_conjSub' hone g (g * B.t * g⁻¹) hgtInv B.t htInv
  -- `h' := n * g`
  refine ⟨n * g, ?_, ?_⟩
  · show n * g ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : n * (g * B.t * g⁻¹) = B.t * n := by
      calc n * (g * B.t * g⁻¹) = n * (g * B.t * g⁻¹) * n⁻¹ * n := by group
        _ = B.t * n := by rw [hnconj]
    calc (n * g) * B.t = n * (g * B.t * g⁻¹) * g := by group
      _ = (B.t * n) * g := by rw [h2]
      _ = B.t * (n * g) := by group
  · rw [conjSub_mul' n g P, ← hg]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNX.symm ▸ hnMg)

end Work.CORE4
