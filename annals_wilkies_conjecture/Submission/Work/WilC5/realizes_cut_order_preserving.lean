/-
  WilC5 — the `L_Rc`-embedding `σ : F → N` of a model `F ⊨ T_R` (a substructure of the model `K`)
  is order preserving with respect to the *order of `K`*.

  `L_Rc` has no relation symbols, so the order of a model of `T_R` is the *definable* order

      `leEL x y  :=  ∃ z, z * z = y - x`

  of `LRcOps.lean`, which coincides with the given `LinearOrder` on every model of `T_R`
  (`leEL_iff_le`).  The content of this file is that this order is respected by any `L_Rc`-hom
  out of a substructure which is itself a model of `T_R`:

  * `map_leEL_of_embedding` : an `L_Rc`-embedding carries `leEL` to `leEL` (it is a homomorphism,
    so it commutes with the ring operations out of which `leEL` is built);

  * the main theorem: for `f g : F` with `(f : K) ≤ (g : K)`, the coercion `F → K` transports a
    square root of `g - f` *in `K`* back to `F` only up to the (totality of) `leEL` on `F`; the
    argument is that `leEL` is total on `F` (`tr_leE_axioms`), so for any two elements either
    `leEL f g` or `leEL g f`; in the second case `(g : K) ≤ (f : K)`, whence `f = g` by
    antisymmetry of the order of `K`, and then `leEL f g` holds by reflexivity.  Applying the
    homomorphism `σ` and transferring back with `leEL_iff_le` in `N` gives the claim.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilC5.tr_leE_axioms
import Submission.Work.WilC5.leEL_iff_le

set_option autoImplicit false

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG FirstOrder Language

/-- An `L_Rc`-embedding (more generally any `L_Rc`-homomorphism) maps the definable order `leEL`
to `leEL`: it commutes with the ring operations defining `leEL`, hence transports the witness. -/
theorem map_leEL_of_embedding {M N : Type} [LRc.Structure M] [LRc.Structure N]
    (e : LRc.Embedding M N) {a b : M} (h : leEL a b) : leEL (e a) (e b) := by
  obtain ⟨z, hz⟩ := h
  have hmul : ∀ x y : M, e (mulEL x y) = mulEL (e x) (e y) := by
    intro x y
    rw [mulEL, Embedding.map_fun, mulEL]
    congr 1
    ext i; fin_cases i <;> rfl
  have hadd : ∀ x y : M, e (addEL x y) = addEL (e x) (e y) := by
    intro x y
    rw [addEL, Embedding.map_fun, addEL]
    congr 1
    ext i; fin_cases i <;> rfl
  have hneg : ∀ x : M, e (negEL x) = negEL (e x) := by
    intro x
    rw [negEL, Embedding.map_fun, negEL]
    congr 1
    ext i; fin_cases i <;> rfl
  have hsub : e (subEL b a) = subEL (e b) (e a) := by
    rw [subEL, subEL, hadd, hneg]
  exact ⟨e z, by rw [← hmul, ← hsub, hz]⟩

theorem realizes_cut_order_preserving {K N : Type}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field N] [LinearOrder N] [IsStrictOrderedRing N] [FirstOrder.Ring.CompatibleRing N]
    [WilkiesDesign.CG.rexpL.Structure N] [(FirstOrder.Language.constantsOn ℝ).Structure N]
    [FirstOrder.Language.Theory.Model N WilkiesDesign.CG.TR]
    (F : WilkiesDesign.CG.LRc.Substructure K) (hF : (F : Type) ⊨ WilkiesDesign.CG.TR)
    (σ : WilkiesDesign.CG.LRc.Embedding F N) :
    ∀ f g : F, (f : K) ≤ (g : K) → (σ f : N) ≤ (σ g : N) := by
  intro f g hfg
  -- `leEL` on `F` (which is a model of `T_R`) is total; the coercion `F → K` reflects it.
  have hFG : leEL f g := by
    rcases (tr_leE_axioms F hF).2.2.2 f g with h | h
    · exact h
    · have hle : (g : K) ≤ (f : K) :=
        (leEL_iff_le (M := K) (inferInstance) (g : K) (f : K)).mp
          (map_leEL_of_embedding F.subtype h)
      have heq : (f : K) = (g : K) := le_antisymm hfg hle
      have hfg' : f = g := Subtype.ext heq
      rw [hfg']
      exact (tr_leE_axioms F hF).1 g
  -- `σ` is a homomorphism, and `leEL` is the order of `N`.
  exact (leEL_iff_le (M := N) (inferInstance) (σ f) (σ g)).mp
    (map_leEL_of_embedding σ hFG)

end Work.WilC5
