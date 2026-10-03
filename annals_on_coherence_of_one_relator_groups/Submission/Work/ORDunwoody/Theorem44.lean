/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# JL Theorem 4.4 (constant-sequence case)

`G` of type `FP₂` over `k`, acting cocompactly on a tree `T`, is dominated by a cocompact
`G`-tree with finitely generated vertex and edge stabilizers.

Proof (JL, §4):  By Bieri–Strebel (`BieriStrebel`, JL Lemma 4.3) there is a surjection
`π : H ↠ G` with `H` finitely presented and `N = ker π` satisfying `N^{ab} ⊗_ℤ k = 0`.
Regard `T` as an `H`-tree through `π`; by the Dunwoody resolution theorem
(`DunwoodyResolution`, GL17 Prop. 2.17, constant case) applied to the finitely presented
group `H`, there is a cocompact `H`-tree `S'` with finitely generated stabilizers which
`π`-dominates `T`.  The descent step `FP2TreePromotion` (Serre §5, JL Lemma 4.1, applied to
the normal closures of `N ∩ H_i` for the vertex stabilizers `H_i` of `S'`, where `N` acts
freely on the quotient and hence is free, and where `N^{ab} ⊗_ℤ k = 0` forces `N = 1`)
converts `S'` into the required `G`-tree.

The two mathematical inputs `DunwoodyResolution` and `FP2TreePromotion` are the parts of
node N13 that are not formalized here; `BieriStrebel` is node N11.  See `Hypotheses.lean`.
-/
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORDunwoody.Promotion
import Submission.Work.ORDunwoody.Lemmas.pullback_isCocompact

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

/-- **JL Theorem 4.4**, in the constant-sequence form needed for Theorem 4.5: if `G` is of
type `FP₂` over `k` and acts cocompactly on a tree `T`, then `T` is dominated by a cocompact
`G`-tree `S` all of whose vertex and edge stabilizers are finitely generated.

Besides Bieri–Strebel (node N11) and the Dunwoody resolution (node N13), this uses the two
node-N12 inputs of the descent step, from which `FP2TreePromotion` is *proved*
(`fp2TreePromotion_of_services`). -/
theorem theorem_4_4 {k : Type u} [CommRing k] [Nontrivial k] {G : Type u} [Group G]
    {V : Type u} [MulAction G V]
    (hBS : BieriStrebel k) (hDR : DunwoodyResolutionAll G)
    (hQ : QuotientTreeByNormalClosureOfElliptic k) (hFree : FreeOnTreeIsFree k)
    (T : GTree G V) (hT : T.IsCocompact) (hfp2 : IsFP2 k G) :
    ∃ (W : Type u) (_ : MulAction G W) (S : GTree G W),
      S.IsCocompact ∧ S.HasFGStab ∧ Dominates S T := by
  obtain ⟨H, instH, π, hπ, hHfp, hker⟩ := (hBS G).mp hfp2
  letI : Group H := instH
  letI : MulAction H V := MulAction.compHom V π
  have hcompat : ∀ (a : H) (v : V), a • v = π a • v := fun _ _ => rfl
  have hT' : (T.pullback π hcompat).IsCocompact :=
    Lemmas.pullback_isCocompact π hπ hcompat T hT
  obtain ⟨W, instW, S', hS'c, hS'fg, hdom⟩ := hDR H (T.pullback π hcompat) hHfp hT'
  letI : MulAction H W := instW
  have hdomOver : DominatesOver π S' T :=
    (dominatesOver_iff_dominates_pullback π hcompat S' T).mpr hdom
  obtain ⟨X, instX, S, hSc, hSfg, hSdom⟩ :=
    fp2TreePromotion_of_services hQ hFree G H π hπ hker T hT S' hS'c hS'fg hdomOver
  exact ⟨X, instX, S, hSc, hSfg, hSdom⟩

/-- JL Theorem 4.4 with the descent step packaged as the single hypothesis
`FP2TreePromotion k`. -/
theorem theorem_4_4_of_promotion {k : Type u} [CommRing k] [Nontrivial k] {G : Type u}
    [Group G] {V : Type u} [MulAction G V]
    (hBS : BieriStrebel k) (hDR : DunwoodyResolutionAll G) (hProm : FP2TreePromotion k)
    (T : GTree G V) (hT : T.IsCocompact) (hfp2 : IsFP2 k G) :
    ∃ (W : Type u) (_ : MulAction G W) (S : GTree G W),
      S.IsCocompact ∧ S.HasFGStab ∧ Dominates S T := by
  obtain ⟨H, instH, π, hπ, hHfp, hker⟩ := (hBS G).mp hfp2
  letI : Group H := instH
  letI : MulAction H V := MulAction.compHom V π
  have hcompat : ∀ (a : H) (v : V), a • v = π a • v := fun _ _ => rfl
  have hT' : (T.pullback π hcompat).IsCocompact :=
    Lemmas.pullback_isCocompact π hπ hcompat T hT
  obtain ⟨W, instW, S', hS'c, hS'fg, hdom⟩ := hDR H (T.pullback π hcompat) hHfp hT'
  letI : MulAction H W := instW
  have hdomOver : DominatesOver π S' T :=
    (dominatesOver_iff_dominates_pullback π hcompat S' T).mpr hdom
  obtain ⟨X, instX, S, hSc, hSfg, hSdom⟩ :=
    hProm G H π hπ hker T hT S' hS'c hS'fg hdomOver
  exact ⟨X, instX, S, hSc, hSfg, hSdom⟩

end Work.ORDunwoody
