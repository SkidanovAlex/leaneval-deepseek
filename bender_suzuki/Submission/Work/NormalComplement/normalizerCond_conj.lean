/-
# Invariance of the `p`-control normaliser condition under `D`-conjugation

Peterfalvi I Ch. III §1 Lemma 2 (the `p`-control criterion) uses, for the `p`-Sylow `P` of
`E = W ⊓ D` and for every non-cyclic `p`-subgroup `U ≤ P`, the normaliser condition

  `N_W(U) = O_{p'}(C_W(U)) · N_E(U)`,

i.e. (with `D = H ⊓ H^t`, so that `N_E(U) = N_W(U) ⊓ W ⊓ D`)

  `N_G(U) ⊓ W = pPrimeCoreSub p (C_G(U) ⊓ W) ⊔ (N_G(U) ⊓ (W ⊓ D))`.

Chapter III §2 (see `SectionsV3.lean`) needs this condition for the `D`-conjugate `U^d` of a
`p`-subgroup `U`, `d ∈ D = twoPoint H t`, and transported back to `U`.  Since `d ∈ H` and `d` lies
in the subgroup `D`, conjugation by `d` fixes both `W` (as `H ≤ N_G(W)`) and `D`; the whole
condition is therefore simply the image of the condition for `U` under the automorphism
`x ↦ d x d⁻¹`.  This file makes that transport formal.

The proof rests on general facts about conjugation by a fixed element `d` (no hypotheses on `d`):

* `eq_map_conj_iff` : `A^d = B^d ↔ A = B`;
* `map_conj_centralizer_gen` : `C_G(U)^d = C_G(U^d)`;
* `map_conj_pPrimeCoreSub_gen` : `O_{p'}(U)^d = O_{p'}(U^d)`;
* `Work.NormalComplement.normalizerCond_transport` assembles them.

`map_conj_pPrimeCoreSub_gen` is the `p`-core statement for an *arbitrary* `p` (the existing
lemmas in the tree assume `p` prime): `O_{p'}(U)` is a supremum of normal subgroups of coprime
order, and `Subgroup.map` of a group isomorphism preserves normality and order, whence
`Work.Fitting.map_sSup` finishes the job.
-/
import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open Classical

namespace Work.NormalComplement

/-! ## Conjugation of the ingredients of the normaliser condition -/

/-- Conjugation by an element of the ambient group preserves the centralizer up to conjugation:
`C_G(U)^d = C_G(U^d)`. -/
lemma map_conj_centralizer_gen {G : Type} [Group G] (X : Subgroup G) (d : G) :
    (Subgroup.centralizer (X : Set G)).map (MulAut.conj d).toMonoidHom
      = Subgroup.centralizer ((X.map (MulAut.conj d).toMonoidHom) : Set G) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    rw [← map_mul, ← map_mul, hc x hx]
  · intro y hy
    set e := MulAut.conj d with he
    refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hx
    have hm : e x ∈ X.map e.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h1 := hy (e x) hm
    have h2 : e (e.symm y * x) = e (x * e.symm y) := by
      rw [map_mul, map_mul, e.apply_symm_apply]; exact h1.symm
    exact e.injective h2.symm

/-- The blueprint's `O_{p'}` commutes with a group isomorphism: `O_{p'}(H)^e = O_{p'}(K)` for
`e : H ≃* K`.  Valid for every `p` (no primality assumption): `O_{p'}` is the supremum of the
normal subgroups of order coprime to `p`, and `Subgroup.map e.toMonoidHom` carries that family
bijectively onto the corresponding family for `K`, preserving normality
(`Subgroup.Normal.map`) and order (`Subgroup.card_map_of_injective`). -/
lemma pPrimeCore_map_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) (p : ℕ) :
    (Submission.Blueprint.pPrimeCore p H).map e.toMonoidHom
      = Submission.Blueprint.pPrimeCore p K := by
  unfold Submission.Blueprint.pPrimeCore
  rw [Work.Fitting.map_sSup]
  congr 1
  ext L
  constructor
  · rintro ⟨L₀, ⟨hn, hc⟩, rfl⟩
    exact ⟨hn.map _ e.surjective, by rw [Subgroup.card_map_of_injective e.injective]; exact hc⟩
  · rintro ⟨hn, hc⟩
    refine ⟨L.map e.symm.toMonoidHom, ⟨hn.map _ e.symm.surjective, ?_⟩, ?_⟩
    · rw [Subgroup.card_map_of_injective e.symm.injective]; exact hc
    · rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K := by ext x; simp
      rw [hcomp, Subgroup.map_id]

/-- `O_{p'}` commutes with conjugation (for every `p`): `O_{p'}(X)^d = O_{p'}(X^d)`. -/
lemma map_conj_pPrimeCoreSub_gen {G : Type} [Group G] (p : ℕ) (X : Subgroup G) (d : G) :
    (Work.NormalComplement.pPrimeCoreSub p X).map (MulAut.conj d).toMonoidHom
      = Work.NormalComplement.pPrimeCoreSub p (X.map (MulAut.conj d).toMonoidHom) := by
  -- `O_{p'}(X)` is the image of `O_{p'}(↥X)` under the inclusion `↥X ↪ G`; conjugation
  -- identifies `↥X` with `↥(X^d)`.
  let e : ↥X ≃* ↥(X.map (MulAut.conj d).toMonoidHom) :=
    X.equivMapOfInjective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective
  have key : Submission.Blueprint.pPrimeCore p ↥(X.map (MulAut.conj d).toMonoidHom) =
      (Submission.Blueprint.pPrimeCore p ↥X).map e.toMonoidHom :=
    (pPrimeCore_map_mulEquiv e p).symm
  show ((Submission.Blueprint.pPrimeCore p ↥X).map X.subtype).map (MulAut.conj d).toMonoidHom =
      (Submission.Blueprint.pPrimeCore p ↥(X.map (MulAut.conj d).toMonoidHom)).map
        (X.map (MulAut.conj d).toMonoidHom).subtype
  rw [key, Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- `A^d = B^d ↔ A = B`: `Subgroup.map` by an injective homomorphism is injective. -/
lemma eq_map_conj_iff {G : Type} [Group G] (d : G) (A B : Subgroup G) :
    A.map (MulAut.conj d).toMonoidHom = B.map (MulAut.conj d).toMonoidHom ↔ A = B :=
  ⟨fun h => Subgroup.map_injective (MulAut.conj d).injective h, fun h => by rw [h]⟩

/-! ## The transport of the normaliser condition -/

/-- If conjugation by `d` fixes `W` and `D`, the normaliser condition is invariant under
replacing `U` by its conjugate `U^d`. -/
lemma normalizerCond_transport {G : Type} [Group G] {D W U : Subgroup G} {p : ℕ} {d : G}
    (hWd : W.map (MulAut.conj d).toMonoidHom = W)
    (hDd : D.map (MulAut.conj d).toMonoidHom = D) :
    (Subgroup.normalizer (U.map (MulAut.conj d).toMonoidHom : Set G) ⊓ W =
      pPrimeCoreSub p
          (Subgroup.centralizer (U.map (MulAut.conj d).toMonoidHom : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U.map (MulAut.conj d).toMonoidHom : Set G) ⊓ (W ⊓ D)))
    ↔ (Subgroup.normalizer (U : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ D))) := by
  -- `conj d` carries the condition for `U` to the condition for `U^d`; compute the image of
  -- every ingredient.
  have hA : (Subgroup.normalizer (U : Set G) ⊓ W).map (MulAut.conj d).toMonoidHom =
      Subgroup.normalizer (U.map (MulAut.conj d).toMonoidHom : Set G) ⊓ W := by
    rw [Subgroup.map_inf (Subgroup.normalizer (U : Set G)) W (MulAut.conj d).toMonoidHom
        (MulAut.conj d).injective,
      Subgroup.map_equiv_normalizer_eq U (MulAut.conj d), hWd]
  have hB : (pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ D))).map (MulAut.conj d).toMonoidHom =
      pPrimeCoreSub p
          (Subgroup.centralizer (U.map (MulAut.conj d).toMonoidHom : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U.map (MulAut.conj d).toMonoidHom : Set G) ⊓ (W ⊓ D)) := by
    rw [Subgroup.map_sup,
      map_conj_pPrimeCoreSub_gen p (Subgroup.centralizer (U : Set G) ⊓ W) d,
      Subgroup.map_inf (Subgroup.centralizer (U : Set G)) W (MulAut.conj d).toMonoidHom
        (MulAut.conj d).injective,
      map_conj_centralizer_gen, hWd,
      Subgroup.map_inf (Subgroup.normalizer (U : Set G)) (W ⊓ D) (MulAut.conj d).toMonoidHom
        (MulAut.conj d).injective,
      Subgroup.map_equiv_normalizer_eq U (MulAut.conj d),
      Subgroup.map_inf W D (MulAut.conj d).toMonoidHom (MulAut.conj d).injective, hWd, hDd]
  have key : (Subgroup.normalizer (U : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ D)))
      ↔ (Subgroup.normalizer (U : Set G) ⊓ W).map (MulAut.conj d).toMonoidHom =
        (pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ D))).map (MulAut.conj d).toMonoidHom :=
    (eq_map_conj_iff d _ _).symm
  rw [key, hA, hB]

/-! ## The requested lemma -/

theorem normalizerCond_conj {G : Type} [Group G] [Finite G] {H : Subgroup G} {t d : G}
    (hd : d ∈ Submission.Blueprint.twoPoint H t) {W : Subgroup G} (hW : W ≤ H)
    (hHn : H ≤ Subgroup.normalizer (W : Set G)) {p : ℕ} {U : Subgroup G} :
    (Subgroup.normalizer (U.map (MulAut.conj d).toMonoidHom : Set G) ⊓ W =
      Work.NormalComplement.pPrimeCoreSub p
        (Subgroup.centralizer (U.map (MulAut.conj d).toMonoidHom : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U.map (MulAut.conj d).toMonoidHom : Set G) ⊓
          (W ⊓ Submission.Blueprint.twoPoint H t)))
    ↔ (Subgroup.normalizer (U : Set G) ⊓ W =
      Work.NormalComplement.pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ (W ⊓ Submission.Blueprint.twoPoint H t))) := by
  -- `d ∈ D = H ⊓ H^t` lies in `H ≤ N_G(W)`, so it fixes `W`; being an element of the subgroup `D`
  -- it also fixes `D`.
  have hd1 : d ∈ H := hd.1
  have hWd : W.map (MulAut.conj d).toMonoidHom = W :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHn hd1)
  have hDd : (Submission.Blueprint.twoPoint H t).map (MulAut.conj d).toMonoidHom =
      Submission.Blueprint.twoPoint H t :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hd)
  exact normalizerCond_transport hWd hDd

end Work.NormalComplement
