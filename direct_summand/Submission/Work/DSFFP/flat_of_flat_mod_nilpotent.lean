import Mathlib
import Submission.Work.DSFFP.Defs
import Submission.Work.DSFFP.tpure_of_flat_quot_top
import Submission.Work.DSFFP.tpure_of_smul_top_le
import Submission.Work.DSFFP.tpure_inclusion_of_comap
import Submission.Work.DSFFP.smul_pow_sup_smul_top_le

namespace Work.DSFFP

universe u

/-- The inclusion `A ↪ B` (`A ≤ B`) followed by `B ↪ Q` is the inclusion `A ↪ Q`. -/
lemma subtype_comp_inclusion {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q]
    [Module S Q] {A B : Submodule S Q} (h : A ≤ B) :
    B.subtype ∘ₗ A.inclusion h = A.subtype := by
  ext x
  rfl

/-- **Induction core of the local flatness criterion (Stacks 10.99.8, tag 051C).**

For every `m`, if `I ^ (m+1)` kills the top of an `S`-module `Q`, then for every submodule `A ≤ Q`
the inclusion `A ↪ Q` stays injective after `⊗[S] T` — assuming the two hypotheses of the criterion
(`h1 : Tor₁ˢ(S ⧸ I, T) = 0`, `h2 : T ⧸ I • ⊤` flat over `S ⧸ I`).

Proof by induction on `m`, using the "gap" `A ⊔ I • ⊤` rather than an intersection: given
`I ^ (m+2) • ⊤ ≤ A`, put `B := A ⊔ I • ⊤`.  Then `I • ⊤ ≤ B`, so `tpure_of_smul_top_le` (Step A)
gives purity of `B ↪ Q`; and `I ^ (m+1) • B ≤ A` (from the `I ^ (m+2)`-condition together with
`I ^ (m+1) • (I • ⊤) = I ^ (m+2) • ⊤`), so the induction hypothesis applied at the ambient module
`↥B` gives purity of the pullback of `A` inside `B`, which is purity of `A ↪ B`
(`tpure_inclusion_of_comap`).  Compose. -/
theorem tpure_of_pow_smul_top_le {S : Type u} [CommRing S] (I : Ideal S) (T : Type u)
    [AddCommGroup T] [Module S T] (h1 : Work.DSFFP.IdxInj I T)
    (h2 : Module.Flat (S ⧸ I) (T ⧸ (I • ⊤ : Submodule S T))) (m : ℕ) :
    ∀ (Q : Type u) [AddCommGroup Q] [Module S Q] (A : Submodule S Q),
      I ^ (m + 1) • (⊤ : Submodule S Q) ≤ A → Work.DSFFP.TPure T A.subtype := by
  induction m with
  | zero =>
    intro Q _ _ A hA
    have hA' : I • (⊤ : Submodule S Q) ≤ A := by simpa using hA
    exact tpure_of_smul_top_le I T h1 h2 A hA'
  | succ m ih =>
    intro Q _ _ A hA
    -- `hA : I ^ (m + 1 + 1) • ⊤ ≤ A`
    set B : Submodule S Q := A ⊔ I • (⊤ : Submodule S Q) with hB
    have hAB : A ≤ B := by rw [hB]; exact le_sup_left
    have hIB : I • (⊤ : Submodule S Q) ≤ B := by rw [hB]; exact le_sup_right
    -- `B ↪ Q` is `T`-pure, by Step A
    have hBpure : Work.DSFFP.TPure T B.subtype := tpure_of_smul_top_le I T h1 h2 B hIB
    -- `I ^ (m+1)` kills `B ⧸ A`
    have hsmul : I ^ (m + 1) • B ≤ A := by
      rw [hB]
      exact smul_pow_sup_smul_top_le I A (m + 1) hA
    -- the same statement, read inside the ambient module `↥B`
    have hcomap : I ^ (m + 1) • (⊤ : Submodule S ↥B) ≤ Submodule.comap B.subtype A := by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top,
        Submodule.range_subtype]
      exact hsmul
    -- induction hypothesis: the pullback of `A` inside `B` is `T`-pure in `B`
    have hApure : Work.DSFFP.TPure T (A.inclusion hAB) :=
      tpure_inclusion_of_comap A B hAB (ih ↥B (Submodule.comap B.subtype A) hcomap)
    rw [show A.subtype = B.subtype ∘ₗ A.inclusion hAB from subtype_comp_inclusion hAB]
    exact hApure.comp hBpure

/-- **Local flatness criterion for a nilpotent ideal (Stacks 10.99.8, tag 051C).**  Let `S` be a commutative ring, `I ⊆ S` an ideal with `I ^ n = ⊥`, and `T` an `S`-module such that the canonical map `I ⊗[S] T → T` is injective (`h1`, i.e. `Tor₁ˢ(S ⧸ I, T) = 0`) and `T ⧸ I • ⊤` is flat over `S ⧸ I` (`h2`).  Then `T` is flat over `S`.

PLAN for the prover.  Prove by induction on `m` that for every `S`-module `Q` with `I ^ m • ⊤ = ⊥` and every submodule `A ≤ Q`, the inclusion `A ↪ Q` is `T`-pure.  (The auxiliary facts are `Work.DSFFP.tpure_of_flat_quot_top` (case `m = 1`, i.e. `Q` killed by `I`) and `Work.DSFFP.tpure_of_smul_top_le` (purity of `A ↪ Q` when `I • ⊤ ≤ A`); both are importable from this directory.)
* `m = 1`: `Q` is killed by `I`, so `tpure_of_flat_quot_top` applies.
* Step: let `I ^ m • ⊤ = ⊥`.  Consider the two short exact sequences `0 → A ⊓ I • ⊤ → A → A ⧸ (A ⊓ I • ⊤) → 0` and `0 → I • ⊤ → Q → Q ⧸ I • ⊤ → 0`.  The induction hypothesis applies to `A ⊓ I • ⊤ ↪ I • ⊤` (as `I ^ m • (I • ⊤) = I ^ (m+1) • ⊤ = ⊥`), the case `m = 1` applies to `A ⧸ (A ⊓ I • ⊤) ↪ Q ⧸ I • ⊤` (both killed by `I`), and `tpure_of_smul_top_le` gives `TPure T (I • ⊤ ↪ Q)` (hypothesis `I • ⊤ ≤ I • ⊤`).  Diagram chase with right exactness of `⊗`: if `z ∈ A ⊗ T` dies in `Q ⊗ T`, its image in `(A ⧸ (A ⊓ I • ⊤)) ⊗ T` dies in `(Q ⧸ I • ⊤) ⊗ T`, hence is `0` by purity of `A ⧸ (A ⊓ I • ⊤) ↪ Q ⧸ I • ⊤`; so `z` comes from `(A ⊓ I • ⊤) ⊗ T` and dies in `I • ⊤ ⊗ T`, hence is `0` by the induction hypothesis (this is the same chase as in `tpure_of_coker_quot`).
Finally, `Module.Flat.iff_rTensor_injective` reduces `Flat S T` to `Injective (J.subtype.rTensor T)` for finitely generated ideals `J ≤ S`, and this is the case `A = J`, `Q = S` of the induction hypothesis (where `I ^ n • ⊤ = ⊥` holds for every module because `I ^ n = ⊥`; note `n = 0` forces `⊤ = ⊥` and the statement is trivial then). -/
theorem flat_of_flat_mod_nilpotent {S : Type _} [CommRing S] (I : Ideal S) (T : Type _)
    [AddCommGroup T] [Module S T] (n : ℕ) (hI : I ^ n = ⊥) (h1 : Work.DSFFP.IdxInj I T)
    (h2 : Module.Flat (S ⧸ I) (T ⧸ (I • ⊤ : Submodule S T))) : Module.Flat S T := by
  -- `I ^ (n+1) = ⊥`, so that the induction (`m + 1`) can start at `m = n`
  have hIn : I ^ (n + 1) = ⊥ := by
    rw [pow_succ, hI, Submodule.bot_mul]
  refine Module.Flat.iff_rTensor_injective'.mpr (fun J => ?_)
  -- `I ^ (n+1) • ⊤ = I ^ (n+1) = ⊥ ≤ J` in the module `S`
  have hJ : I ^ (n + 1) • (⊤ : Submodule S S) ≤ J := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hIn]
    exact bot_le
  exact tpure_of_pow_smul_top_le I T h1 h2 n S J hJ

end Work.DSFFP
