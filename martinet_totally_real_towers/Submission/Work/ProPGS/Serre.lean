import Submission.Work.ProPGS.CommonsBridge

/-!
# `Work.ProPGS.Serre` -- the Serre/Euler-characteristic engine with a *spanning* relator set

**Namespace** `Work.ProPGS`; module `Submission.Work.ProPGS.Serre`.

`Commons.GroupTheory.ProPGroup` proves the finite-`p`-group Golod--Shafarevich inequality for a
presentation `⟨α | rel⟩` of a finite `p`-group `Q`: `4 · |rel| > |α|²`.  The only place the
relator set enters the *proof* is

* `ker Φ ≤ range (dRel rel)`, where `Φ : (α → 𝔽_p[Q]) → 𝔽_p[Q]` is the Koszul differential and
  `dRel` is the Fox-differential map out of the relator module (this is the exactness of the Fox
  resolution), and
* the *shift* property `dRel (∏_rel bG^m) ⊆ ∏_α bG^{m+1}`, which holds as soon as every relator in
  the set is a genuine relator (lies in the kernel of the presentation map).

Both are available for a set `S` that merely *spans* the relation kernel modulo its
relation-Frattini subgroup `K^p[K,F]` (the pro-`p` situation, where the defect is a pro-`p` group and
Nakayama applies), so the whole Serre argument runs with `|S|` in place of `|rel|`.  This file
supplies the two placeholders for `S`:

* `Work.ProPGS.kappa_mem_IW_sq_of_mem_ker`, `Work.ProPGS.rho_Dlin_kappa_mem_bG_of_mem_ker`,
  `Work.ProPGS.dRel_mem_pi_pow_of_mem_ker` -- the shift property for a set of actual relators;
* `Work.ProPGS.serre_equality'` -- the Serre equality `|α|·A(k+1) + 1 = A(k+2) + dim T_k`, copied
  from the commons with its irrelevant `normalClosure rel = ker π` hypothesis removed.

The downstream consumers are `Work.ProPGS.finrank_Tq_le_card_mul` (the `|S|·A(k)` bound on `T_k`) and
`Submission/Work/ProPGS/Unconditional.lean` (the final assembly).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.ProPGS

open Commons.GroupTheory.ProPGroup

/-- **Relators have Zassenhaus degree `≥ 2`** (the `π u = 1` form of
`Commons.GroupTheory.ProPGroup.ScratchSerre.kappa_mem_IW_sq`): for `u ∈ ker π`,
`κ(u) = [u] - 1 ∈ IW²` in the group algebra of the free group. -/
theorem kappa_mem_IW_sq_of_mem_ker {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Fintype G]
    {α : Type*} [Fintype α] [DecidableEq α] (hG : IsPGroup p G) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {u : FreeGroup α} (hu : u ∈ MonoidHom.ker π) :
    Commons.GroupTheory.ProPGroup.ScratchSerre.kappa p α u ∈ ScratchGS.IW p α ^ 2 := by
  haveI : Finite G := Finite.of_fintype G
  have h := Commons.GroupTheory.ProPGroup.sub_one_mem_gsIW_sq_of_mem_ker (p := p) (α := α)
    (G := G) hG π hπ hgen hu
  have hIW : Commons.GroupTheory.ProPGroup.gsIW p α = ScratchGS.IW p α := rfl
  rw [hIW] at h
  simpa [Commons.GroupTheory.ProPGroup.ScratchSerre.kappa] using h

/-- **The Fox derivative of a relator has augmentation degree `≥ 1`**: for `u ∈ ker π` and `i : α`,
`ρ(D_i κ(u)) ∈ bG`. -/
theorem rho_Dlin_kappa_mem_bG_of_mem_ker {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Fintype G]
    {α : Type*} [Fintype α] [DecidableEq α] (hG : IsPGroup p G) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {u : FreeGroup α} (hu : u ∈ MonoidHom.ker π) (i : α) :
    Commons.GroupTheory.ProPGroup.rho p α π
        (ScratchGS.Dlin p α i (Commons.GroupTheory.ProPGroup.ScratchSerre.kappa p α u))
      ∈ Commons.GroupTheory.ProPGroup.ScratchSerre.bG p G := by
  have hmem := Commons.GroupTheory.ProPGroup.ScratchSerre.Dlin_mem_IW_pow_succ p α i (k := 1)
    (kappa_mem_IW_sq_of_mem_ker hG π hπ hgen hu)
  rw [Submodule.pow_one (ScratchGS.IW p α)] at hmem
  exact Commons.GroupTheory.ProPGroup.ScratchSerre.rho_mem_bG p G α π hmem

/-- **The shift property** for a finite set `S` of actual relators: `dRel` maps `∏_S bG^m` into
`∏_α bG^{m+1}`. -/
theorem dRel_mem_pi_pow_of_mem_ker {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Fintype G]
    {α : Type*} [Fintype α] [DecidableEq α] (hG : IsPGroup p G) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    (S : Finset (FreeGroup α)) (hS : ∀ s ∈ S, π s = 1) (m : ℕ)
    {f : ↥S → MonoidAlgebra (ZMod p) G}
    (hf : f ∈ Submodule.pi Set.univ
      (fun _ : ↥S => Submodule.restrictScalars (ZMod p)
        (Commons.GroupTheory.ProPGroup.ScratchSerre.bG p G ^ m))) :
    Commons.GroupTheory.ProPGroup.ScratchSerre.dRel p α G S π f ∈
      Submodule.pi Set.univ (fun _ : α => Submodule.restrictScalars (ZMod p)
        (Commons.GroupTheory.ProPGroup.ScratchSerre.bG p G ^ (m + 1))) := by
  rw [Submodule.mem_pi]
  intro i _
  show (∑ r : ↥S, f r * Commons.GroupTheory.ProPGroup.rho p α π
      (ScratchGS.Dlin p α i (Commons.GroupTheory.ProPGroup.ScratchSerre.kappa p α (r : FreeGroup α))))
    ∈ Submodule.restrictScalars (ZMod p)
        (Commons.GroupTheory.ProPGroup.ScratchSerre.bG p G ^ (m + 1))
  rw [Submodule.pow_succ]
  refine Ideal.sum_mem _ (fun r _ => ?_)
  exact Ideal.mul_mem_mul ((Submodule.mem_pi.mp hf) r (Set.mem_univ r))
    (rho_Dlin_kappa_mem_bG_of_mem_ker hG π hπ hgen
      (MonoidHom.mem_ker.mpr (hS r r.2)) i)

/-- **The Serre equality.** `|α| · A(k+1) + 1 = A(k+2) + dim T_k`, where
`A n = dim 𝔽_p[Q] / bG^n` and `T_k = (ker Φ + ∏_α bG^{k+1}) / ∏_α bG^{k+1}`.

This is `Commons.GroupTheory.ProPGroup.ScratchSerre.serre_equality` with its (unused) hypothesis
`normalClosure rel = ker π` removed: the stated identity does not mention the relator set at all. -/
theorem serre_equality' {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Fintype G]
    {α : Type*} [Fintype α] [DecidableEq α] (hG : IsPGroup p G) (π : FreeGroup α →* G)
    (hπ : Function.Surjective π)
    (hgen : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    (k : ℕ) :
    Fintype.card α * Commons.GroupTheory.ProPGroup.ScratchSerre.Abar p G (k + 1) + 1 =
      Commons.GroupTheory.ProPGroup.ScratchSerre.Abar p G (k + 2) +
        Module.finrank (ZMod p)
          ↥(Commons.GroupTheory.ProPGroup.ScratchSerre.Tq p G α π k) := by
  have h1 := Commons.GroupTheory.ProPGroup.ScratchSerre.finrank_quot_P_add p G α π k
  have h2 := Commons.GroupTheory.ProPGroup.ScratchSerre.finrank_quot_T_eq p G α π k
  have h3 := Commons.GroupTheory.ProPGroup.ScratchSerre.finrank_quot_pi_pow p G α k
  have h4 := Commons.GroupTheory.ProPGroup.ScratchSerre.finrank_quot_Q p G α π hπ (k + 1)
  have h3' : Module.finrank (ZMod p)
      ((α → MonoidAlgebra (ZMod p) G) ⧸
        Commons.GroupTheory.ProPGroup.ScratchSerre.Ppow p G α (k + 1)) =
      Fintype.card α * Commons.GroupTheory.ProPGroup.ScratchSerre.Abar p G (k + 1) := by
    simpa [Commons.GroupTheory.ProPGroup.ScratchSerre.Ppow,
      Commons.GroupTheory.ProPGroup.ScratchSerre.Abar] using h3
  have h4' : Module.finrank (ZMod p)
      ((α → MonoidAlgebra (ZMod p) G) ⧸
        Commons.GroupTheory.ProPGroup.ScratchSerre.Qker p G α π (k + 1)) =
      Commons.GroupTheory.ProPGroup.ScratchSerre.Abar p G (k + 2) - 1 := by
    simpa [Commons.GroupTheory.ProPGroup.ScratchSerre.Ppow,
      Commons.GroupTheory.ProPGroup.ScratchSerre.Qker,
      Commons.GroupTheory.ProPGroup.ScratchSerre.Abar] using h4
  have key : Module.finrank (ZMod p)
      ((α → MonoidAlgebra (ZMod p) G) ⧸
        Commons.GroupTheory.ProPGroup.ScratchSerre.Ppow p G α (k + 1)) =
      Module.finrank (ZMod p)
        (((α → MonoidAlgebra (ZMod p) G) ⧸
          Commons.GroupTheory.ProPGroup.ScratchSerre.Ppow p G α (k + 1)) ⧸
            Commons.GroupTheory.ProPGroup.ScratchSerre.Tq p G α π k) +
        Module.finrank (ZMod p)
          ↥(Commons.GroupTheory.ProPGroup.ScratchSerre.Tq p G α π k) := h1.symm
  rw [h3', h2, h4'] at key
  have hge : 1 ≤ Commons.GroupTheory.ProPGroup.ScratchSerre.Abar p G (k + 2) :=
    Commons.GroupTheory.ProPGroup.ScratchSerre.Abar_pos p G (by omega)
  omega

end Work.ProPGS
