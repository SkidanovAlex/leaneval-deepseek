import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.ch1_lem2
import Submission.Work.ThreePoints.even_card_centralizer_of_fixes_three

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs

/-- **The reduction that isolates the content of Ch. II §4 Prop. 1 (a).**

Let `H` be a strongly embedded subgroup of the finite group `G`, `X ≤ M = H^g` a subgroup fixing
at least three points of `Ω = G ⧸ H`.  If *some involution `u ∈ M` normalises `X`*, then `C_M(X)`
has even order.

The proof is one application of Theorem C (`Submission.Blueprint.ThmCProp`, hypothesis `hC`):
`M` is strongly embedded (it is a conjugate of `H`) and `X ≤ M ⊓ M₂` for any *second* fixed point
`M₂ = conj g₂ H ≠ M` of `X` (such a point exists because `|fixedPts H X| ≥ 3`); since
`u ∈ inv(M)` normalises `X`, Theorem C says `u` centralises `X`, so `u` is an involution of
`M ⊓ C_G(X)`.

Thus the whole remaining content of `prop1a_even_card_centralizer` is the existence of an
involution of `M` normalising `X` (equivalently: `N_M(X) = M ⊓ N_G(X)` has even order).  In the
source this is Ch. I §4 Prop. 2 applied inside `F₁ = C_G(O^p(X))·P`; its `2`-rank-`1` case is
precisely the Brauer–Suzuki theorem (`Submission.Blueprint.BrauerSuzukiProp`). -/
theorem prop1a_of_involution_normalizing {G : Type} [Group G] [Finite G]
    (hC : Submission.Blueprint.ThmCProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M)
    (hu : ∃ u : G, u ∈ M ∧ u ∈ Subgroup.normalizer (X : Set G) ∧ orderOf u = 2) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) := by
  classical
  obtain ⟨g₀, hg₀⟩ := hM
  obtain ⟨u, huM, huN, hu2⟩ := hu
  -- the point `ω₀ = g₀H` whose stabiliser is `M`
  have hStab0 : MulAction.stabilizer G (g₀ : G ⧸ H) = M := by
    rw [hg₀, Work.ThreePoints.stabilizer_mk]
  -- a second fixed point of `X`
  have h2 : 1 < (Submission.Blueprint.fixedPts H X).ncard := by omega
  obtain ⟨ω₂, hω₂, hne⟩ := Set.exists_ne_of_one_lt_ncard h2 (g₀ : G ⧸ H)
  obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective ω₂
  have hStab2 : MulAction.stabilizer G ω₂ = Submission.Blueprint.conj g₂ H := by
    rw [← hg₂, Work.ThreePoints.stabilizer_mk]
  have hX2 : X ≤ MulAction.stabilizer G ω₂ :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₂
  -- its stabiliser differs from `M`
  have hM2ne : MulAction.stabilizer G ω₂ ≠ M := by
    intro heq
    have hpt : (g₀ : G ⧸ H) = ω₂ := by
      rw [← hg₂]
      refine Work.ThreePoints.mk_eq_of_conj_eq hH ?_
      exact hg₀.symm.trans (hStab2.symm.trans heq).symm
    exact hne hpt.symm
  have hMstrong : IsStronglyEmbedded M := by
    rw [hg₀]; exact Work.ThreePoints.conj_stronglyEmbedded hH g₀
  -- `M₂ = conj g M` for `g = g₂ * g₀⁻¹`, with `g ∉ M`
  obtain ⟨g, hgdef⟩ : ∃ g : G, g = g₂ * g₀⁻¹ := ⟨_, rfl⟩
  have hconjg : Submission.Blueprint.conj g M = MulAction.stabilizer G ω₂ := by
    rw [hgdef, hg₀, Work.DoubleTransitivity.conj_mul, Work.DoubleTransitivity.conj_inv_conj,
      hStab2]
  have hgnotMem : g ∉ M := by
    intro hgmem
    have h1 : Submission.Blueprint.conj g M = M := Work.ThreePoints.conj_eq_self_of_mem hgmem
    exact hM2ne (hconjg.symm.trans h1)
  -- Theorem C: `u` centralises `X`
  have hcent : ∀ x ∈ X, u * x = x * u :=
    hC G hS M hMstrong g hgnotMem u ⟨huM, hu2⟩ X (le_inf hXM (hconjg ▸ hX2)) huN
  -- hence `u` is an involution of `M ⊓ C_G(X)`
  refine even_iff_two_dvd.mpr ?_
  have hmem : u ∈ (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
    ⟨huM, Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcent x hx).symm)⟩
  have hord : orderOf (⟨u, hmem⟩ :
      ↥(M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hu2
  have hdvd := orderOf_dvd_natCard
    (⟨u, hmem⟩ : ↥(M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
  rwa [hord] at hdvd

/-- Peterfalvi I Ch. II §4 Prop. 1 (a): under (B0)–(B2), if `X` fixes at least three points of `Ω = G ⧸ H` and `M` is one of them (`M = H^g ⊇ X`), then `C_M(X)` has even order.

This is the shape in which the (now unconditional) Prop. 1 (a) `Work.ThreePoints.even_card_centralizer_of_fixes_three` was first requested; it is recorded here as a corollary of that theorem.  The source's proof is the strong induction on `|X|` carried out in `Work.ThreePoints.prop1a_aux` (whose step is `Work.ThreePoints.prop1a_descent`), with Theorem C (`hC`) and Theorem A (`hA`) as the two external inputs. -/
theorem prop1a_even_card_centralizer {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  Work.ThreePoints.even_card_centralizer_of_fixes_three hFT hC hA hS hH hX3 hM hXM

end Work.ThreePoints
