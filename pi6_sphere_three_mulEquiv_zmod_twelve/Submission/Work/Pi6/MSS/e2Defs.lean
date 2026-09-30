import Mathlib
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.Pages
import Submission.Work.Pi6.MSS.PagesComp
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.AssembleDefs
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Vocabulary for the multiplicative `E_2` page of the Serre spectral sequence

This file fixes the two objects in terms of which the multiplicative structure of the `E_2` page is
stated:

* `Work.Pi6.MSS.Koszul Φ` — the assertion that a family of isomorphisms
  `Φ_{s,q} : E_2^{s,q} ≅ H^s(B;𝕜) ⊗ H^q(F;𝕜)` of the concrete `E_2` page `pEraw` of the Serre
  cochain filtration of `p` turns the product `pd_mul 2` of the page into the **Koszul tensor
  product** of the cup products of `B` and of the fibre `F = p⁻¹(p e₀)`;
* `Work.Pi6.MSS.e2Of Φ` — the same identification transported to the page `A.S.E 2` of an assembled
  spectral sequence `A : Assembled 𝕜 (serreCF 𝕜 E B p) D` through the assembly isomorphism `A.iso`.

The main consequence (proved in `Submission/Work/Pi6/MSS/e2Mul.lean`) is

* `Work.Pi6.MSS.e2Of_mul` — clause 1 of `Work.Pi6.MSS.e2Mul`: for any Koszul `Φ`, the product
  `A.S.mul 2` of the assembled page is the Koszul product; it is the transport of `pd_mul` through
  `A.mul_compat` and `Work.Pi6.MSS.mulEq`.

The remaining clauses of `e2Mul` (the base and fibre edge clauses) are stated separately as
`e2EdgeBase`/`e2EdgeFibre`; together with the existence of a Koszul family
(`Work.Pi6.MSS.e2AddKoszul`) they give `e2Mul`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The fibre `F = p⁻¹(p e₀)` of `p` at `e₀`. -/
abbrev e2Fib {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) : Type :=
  Work.StemsB.fibre p (p e₀)

/-- The module `H^s(B;𝕜) ⊗ H^q(F;𝕜)`, the target of the `E_2` identification. -/
abbrev e2Tens (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (s q : ℕ) : ModuleCat 𝕜 :=
  ModuleCat.of 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s) (Work.Pi6.Coh 𝕜 (e2Fib p e₀) q))

/-- A family of isomorphisms identifying the concrete `E_2` page of `p` with
`H^s(B;𝕜) ⊗ H^q(F;𝕜)` through total degree `N`. -/
abbrev e2Family (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) : Type :=
  ∀ (s q : ℕ), s ≤ N → q ≤ N →
    (pEraw 𝕜 (serreCF 𝕜 E B p) 2 s (s + q) ≅ e2Tens 𝕜 p e₀ s q)

/-- **The Koszul multiplicativity rule** for an additive identification `Φ` of the `E_2` page: the
product of the concrete page is the Koszul tensor product of the cup products on the base and on the
fibre. -/
def Koszul (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (Φ : e2Family 𝕜 E B p e₀ N) : Prop :=
  ∀ (s q s' q' : ℕ) (hs : s ≤ N) (hq : q ≤ N) (hs' : s' ≤ N) (hq' : q' ≤ N)
    (b : Work.Pi6.Coh 𝕜 B s) (f : Work.Pi6.Coh 𝕜 (e2Fib p e₀) q)
    (b' : Work.Pi6.Coh 𝕜 B s') (f' : Work.Pi6.Coh 𝕜 (e2Fib p e₀) q')
    (hss : s + s' ≤ N) (hqq : q + q' ≤ N),
    (pEcastN 𝕜 (serreCF 𝕜 E B p) 2 (s + s') (by omega)).hom
        (pd_mul 2 s (s + q) s' (s' + q')
          ((Φ s q hs hq).inv.hom (b ⊗ₜ[𝕜] f))
          ((Φ s' q' hs' hq').inv.hom (b' ⊗ₜ[𝕜] f')))
      = ((-1 : 𝕜) ^ (q * s')) •
          (Φ (s + s') (q + q') hss hqq).inv.hom
            ((Work.Pi6.cup 𝕜 B s s' b b') ⊗ₜ[𝕜]
              (Work.Pi6.cup 𝕜 (e2Fib p e₀) q q' f f'))

/-- The `r = 2` assembly isomorphism, with the proof argument fixed (`A.iso` is a function of the
proof of `2 ≤ 2`, so its values only depend on `A` by proof irrelevance). -/
def isoTwo {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} {D : PagesData 𝕜 (serreCF 𝕜 E B p)}
    (A : Assembled 𝕜 (serreCF 𝕜 E B p) D) (s q : ℕ) :
    A.S.E 2 ((s : ℤ), (q : ℤ)) ≅ pEraw 𝕜 (serreCF 𝕜 E B p) 2 s (s + q) :=
  A.iso 2 s q (by norm_num)

/-- The assembly isomorphism `A.iso 2` does not depend on the proof of `2 ≤ 2`. -/
theorem isoTwo_eq {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} {D : PagesData 𝕜 (serreCF 𝕜 E B p)}
    (A : Assembled 𝕜 (serreCF 𝕜 E B p) D) (s q : ℕ) (h : 2 ≤ 2) :
    A.iso 2 s q h = isoTwo A s q :=
  congrArg (fun hh : 2 ≤ 2 => A.iso 2 s q hh) (Subsingleton.elim h (by norm_num))

/-- The identification of the page `A.S.E 2` of an assembled spectral sequence induced by a family
`Φ` of isomorphisms of the concrete page: the composite of the assembly isomorphism `A.iso` with
`Φ`. -/
def e2Of {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} {e₀ : E} {N : ℕ}
    {D : PagesData 𝕜 (serreCF 𝕜 E B p)} (A : Assembled 𝕜 (serreCF 𝕜 E B p) D)
    (Φ : e2Family 𝕜 E B p e₀ N) (s q : ℕ) (hs : s ≤ N) (hq : q ≤ N) :
    A.S.E 2 ((s : ℤ), (q : ℤ)) ≅ e2Tens 𝕜 p e₀ s q :=
  (isoTwo A s q).trans (Φ s q hs hq)

/-- The inverse of `e2Of` computes through the assembly isomorphism and `Φ`. -/
@[simp] theorem e2Of_inv_apply {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] {p : C(E, B)} {e₀ : E} {N : ℕ}
    {D : PagesData 𝕜 (serreCF 𝕜 E B p)} {A : Assembled 𝕜 (serreCF 𝕜 E B p) D}
    (Φ : e2Family 𝕜 E B p e₀ N) (s q : ℕ) (hs : s ≤ N) (hq : q ≤ N)
    (x : e2Tens 𝕜 p e₀ s q) :
    (isoTwo A s q).hom ((e2Of A Φ s q hs hq).inv.hom x) = (Φ s q hs hq).inv.hom x := by
  simp only [e2Of, Iso.trans_inv, Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [Iso.inv_hom_id_apply]

end

end Work.Pi6.MSS
