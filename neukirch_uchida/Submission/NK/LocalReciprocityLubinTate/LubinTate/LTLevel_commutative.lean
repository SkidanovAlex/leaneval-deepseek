import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.ltLevelIsSimple
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_smul2
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_mem
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_algEquiv
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isGalois_LTLevel
import Submission.NK.LocalReciprocityLubinTate.LubinTate.map_mem_LTdivisionSet_of_algEquiv
import Submission.NK.LocalReciprocityLubinTate.LubinTate.ext_of_eqOn_LTdivisionSet

/-!
# The Lubin–Tate level is an abelian extension

The Galois group of the `n`-th Lubin–Tate level `K_n = F(Λ_n)` is commutative: classically
`Gal(K_n/F) ≅ (𝒪[F]/π^n)^×` (Milne, *CFT*, Theorem I.3.1 and 3.6 (b); Serre, *Local Fields*,
Ch. XV §4).

The proof here uses the `𝒪[F]`-module structure of the torsion points `Λ_n` established in
`Submission/Work/LocalReciprocityLubinTate/Eval/`:

* `Λ_n = {a · y : a ∈ 𝒪[F]}` for any primitive `y ∈ Λ_n ∖ Λ_{n-1}`
  (`Eval.range_smulDiv_eq_LTdivisionSet`), and `K_n = F(y)` for such a `y`
  (`ltLevelIsSimple_residueCard`);
* every `F`-automorphism of `K_n` extends to an `F`-automorphism of the algebraic closure
  (`AlgEquiv.liftNormal`), and is therefore `𝒪[F]`-linear for the action `a · x`
  (`Eval.smulDiv_algEquiv`);
* that action is associative (`Eval.smulDiv_smul2`).

So for `σ, τ ∈ Gal(K_n/F)` with `σ y = a · y`, `τ y = b · y` one computes
`(σ τ) y = σ (b · y) = b · (a · y) = (b a) · y` and `(τ σ) y = (a b) · y`, and `𝒪[F]` is
commutative; since `y` generates `K_n`, this gives `σ τ = τ σ`.
-/

namespace NK.LocalReciprocityLubinTate.LubinTate

open Polynomial

set_option maxHeartbeats 800000

/-- An `F`-algebra automorphism of the algebraic closure permutes the `π^n`-division points: a root
of the iterate `f^{(n)}` (a polynomial with coefficients in `F`) is sent to a root of `f^{(n)}`. -/
theorem map_mem_LTdivisionSet_of_algEquiv_closure {F : Type*} [Field F]
    (π : F) (q n : ℕ) (hq : 2 ≤ q)
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) {x : AlgebraicClosure F}
    (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F π q n) :
    σ x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F π q n := by
  rw [NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff π q n hq] at hx ⊢
  rw [Polynomial.aeval_algHom_apply]
  rw [hx, map_zero]

theorem LTLevel_commutative {F : Type*} [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) :
    ∀ σ τ : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n) ≃ₐ[F]
      ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n), σ * τ = τ * σ := by
  classical
  -- the Lubin–Tate formal group of `π` over `𝒪[F]`
  obtain ⟨M, hpi⟩ := NK.LocalReciprocityLubinTate.lubinTateModule_integers F π hπ
  have hq : 2 ≤ NK.LocalReciprocityLubinTate.residueCard F :=
    NK.LocalReciprocityLubinTate.two_le_residueCard F
  -- a primitive `π^n`-division point
  obtain ⟨y, hy, hy'⟩ : ∃ y : AlgebraicClosure F,
      y ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n ∧
      y ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) := by
    by_contra h
    push Not at h
    have hsub : NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n ⊆
        NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) := h
    have heq : NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n =
        NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) :=
      Set.Subset.antisymm hsub (NK.LocalReciprocityLubinTate.LTdivisionSet_mono F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) hq (Nat.sub_le n 1))
    have h1 := NK.LocalReciprocityLubinTate.ncard_LTdivisionSet F π hπ
      (NK.LocalReciprocityLubinTate.residueCard F) n hq
    have h2 := NK.LocalReciprocityLubinTate.ncard_LTdivisionSet F π hπ
      (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) hq
    rw [heq, h2] at h1
    have hlt : (NK.LocalReciprocityLubinTate.residueCard F) ^ (n - 1) <
        (NK.LocalReciprocityLubinTate.residueCard F) ^ n :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    exact (ne_of_lt hlt) h1
  -- `y` generates the level
  have hgen : NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n
      = IntermediateField.adjoin F ({y} : Set (AlgebraicClosure F)) :=
    NK.LocalReciprocityLubinTate.LTLevel_eq_adjoin_singleton_of_isSimple
      (NK.LocalReciprocityLubinTate.ltLevelIsSimple_residueCard π hπ n hn) hy hy'
  intro σ τ
  -- the multiplication by `a` on the torsion points
  let Φ : ↥(ValuativeRel.valuation F).integer → AlgebraicClosure F := fun c =>
    NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
      (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy c
  -- the lifts of `σ` and `τ` to the algebraic closure
  let σ' : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ.liftNormal (AlgebraicClosure F)
  let τ' : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := τ.liftNormal (AlgebraicClosure F)
  have hσcomm : ∀ x : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n),
      σ' (x : AlgebraicClosure F) = ((σ x : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n)) : AlgebraicClosure F) := fun x =>
    AlgEquiv.liftNormal_commutes σ (AlgebraicClosure F) x
  have hτcomm : ∀ x : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n),
      τ' (x : AlgebraicClosure F) = ((τ x : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n)) : AlgebraicClosure F) := fun x =>
    AlgEquiv.liftNormal_commutes τ (AlgebraicClosure F) x
  -- the images of `y` are again division points, hence multiples of `y`
  have hσ'y : σ' y ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n :=
    map_mem_LTdivisionSet_of_algEquiv_closure (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n hq σ' hy
  have hτ'y : τ' y ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n :=
    map_mem_LTdivisionSet_of_algEquiv_closure (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n hq τ' hy
  obtain ⟨a, ha0⟩ : ∃ a : ↥(ValuativeRel.valuation F).integer, Φ a = σ' y := by
    have hrange := NK.LocalReciprocityLubinTate.Eval.range_smulDiv_eq_LTdivisionSet π hπ
      (NK.LocalReciprocityLubinTate.residueCard F) n hq hn rfl M hpi hy hy'
    exact Set.mem_range.mp (show σ' y ∈ Set.range (fun c : ↥(ValuativeRel.valuation F).integer =>
        NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy c) from hrange ▸ hσ'y)
  have ha : σ' y = Φ a := ha0.symm
  obtain ⟨b, hb0⟩ : ∃ b : ↥(ValuativeRel.valuation F).integer, Φ b = τ' y := by
    have hrange := NK.LocalReciprocityLubinTate.Eval.range_smulDiv_eq_LTdivisionSet π hπ
      (NK.LocalReciprocityLubinTate.residueCard F) n hq hn rfl M hpi hy hy'
    exact Set.mem_range.mp (show τ' y ∈ Set.range (fun c : ↥(ValuativeRel.valuation F).integer =>
        NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy c) from hrange ▸ hτ'y)
  have hb : τ' y = Φ b := hb0.symm
  -- `𝒪[F]`-linearity of `σ'` and `τ'`
  have hkeyL : ∀ c : ↥(ValuativeRel.valuation F).integer, σ' (Φ c) = Φ (c * a) := by
    intro c
    have h1 : σ' (Φ c) = NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n hq M hσ'y c :=
      NK.LocalReciprocityLubinTate.Eval.smulDiv_algEquiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n hq M y hy σ' hσ'y c
    have h2 : NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M hσ'y c =
        NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M
          (NK.LocalReciprocityLubinTate.Eval.smulDiv_mem π hπ
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy a) c := by
      have hpair : (⟨σ' y, hσ'y⟩ : {x : AlgebraicClosure F //
            x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n}) =
          ⟨NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
              (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy a,
            NK.LocalReciprocityLubinTate.Eval.smulDiv_mem π hπ
              (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy a⟩ :=
        Subtype.ext ha
      exact congrArg (fun p : {x : AlgebraicClosure F //
          x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n} =>
        NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M p.2 c) hpair
    have h3 : NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M
          (NK.LocalReciprocityLubinTate.Eval.smulDiv_mem π hπ
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy a) c =
        Φ (c * a) :=
      NK.LocalReciprocityLubinTate.Eval.smulDiv_smul2 π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy c a
    exact h1.trans (h2.trans h3)
  have hkeyR : ∀ c : ↥(ValuativeRel.valuation F).integer, τ' (Φ c) = Φ (c * b) := by
    intro c
    have h1 : τ' (Φ c) = NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n hq M hτ'y c :=
      NK.LocalReciprocityLubinTate.Eval.smulDiv_algEquiv π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n hq M y hy τ' hτ'y c
    have h2 : NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M hτ'y c =
        NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M
          (NK.LocalReciprocityLubinTate.Eval.smulDiv_mem π hπ
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy b) c := by
      have hpair : (⟨τ' y, hτ'y⟩ : {x : AlgebraicClosure F //
            x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n}) =
          ⟨NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
              (NK.LocalReciprocityLubinTate.residueCard F) n hq M hy b,
            NK.LocalReciprocityLubinTate.Eval.smulDiv_mem π hπ
              (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy b⟩ :=
        Subtype.ext hb
      exact congrArg (fun p : {x : AlgebraicClosure F //
          x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
            (NK.LocalReciprocityLubinTate.residueCard F) n} =>
        NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M p.2 c) hpair
    have h3 : NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ
          (NK.LocalReciprocityLubinTate.residueCard F) n hq M
          (NK.LocalReciprocityLubinTate.Eval.smulDiv_mem π hπ
            (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy b) c =
        Φ (c * b) :=
      NK.LocalReciprocityLubinTate.Eval.smulDiv_smul2 π hπ
        (NK.LocalReciprocityLubinTate.residueCard F) n hq M hpi y hy c b
    exact h1.trans (h2.trans h3)
  -- it suffices to check the identity at the generator `y`
  have key_y : ∀ z : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) n),
      (z : AlgebraicClosure F) = y → (σ * τ) z = (τ * σ) z := by
    intro z hz
    apply Subtype.ext
    have hL : (((σ * τ) z : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n)) : AlgebraicClosure F) = Φ (b * a) := by
      calc (((σ * τ) z : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n)) : AlgebraicClosure F)
          = σ' (τ' ((z : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n)) : AlgebraicClosure F)) := by
            rw [AlgEquiv.mul_apply, ← hσcomm (τ z), ← hτcomm z]
        _ = σ' (τ' y) := by rw [hz]
        _ = σ' (Φ b) := by rw [hb]
        _ = Φ (b * a) := hkeyL b
    have hR : (((τ * σ) z : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
        (NK.LocalReciprocityLubinTate.residueCard F) n)) : AlgebraicClosure F) = Φ (a * b) := by
      calc (((τ * σ) z : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n)) : AlgebraicClosure F)
          = τ' (σ' ((z : ↥(NK.LocalReciprocityLubinTate.LTLevel F (π : F)
              (NK.LocalReciprocityLubinTate.residueCard F) n)) : AlgebraicClosure F)) := by
            rw [AlgEquiv.mul_apply, ← hτcomm (σ z), ← hσcomm z]
        _ = τ' (σ' y) := by rw [hz]
        _ = τ' (Φ a) := by rw [ha]
        _ = Φ (a * b) := hkeyR a
    rw [hL, hR, mul_comm]
  have hhom : (σ * τ).toAlgHom = (τ * σ).toAlgHom := by
    refine IntermediateField.algHom_ext_of_eq_adjoin (F := F) hgen ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact key_y _ rfl
  exact AlgEquiv.coe_toAlgHom_injective hhom

end NK.LocalReciprocityLubinTate.LubinTate
