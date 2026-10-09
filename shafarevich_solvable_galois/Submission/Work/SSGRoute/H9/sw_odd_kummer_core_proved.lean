import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst
import Submission.Work.SSGRoute.H9.swZSixDef
import Submission.Work.SSGRoute.ZDataMup.sw_odd_kummer_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The odd-`p` Kummer core of Schmidt–Wingberg §4 (node `Work.SSGRoute.H9`)

The node's statement (below, verbatim) is `Work.SSGRoute.sw_odd_kummer_core`, i.e. Schmidt–Wingberg
§4 in the case `A = μ_p` for odd `p` (arXiv:math/9809211, Theorem 13).  It is the Z-side arithmetic
input of `Work.SSGRoute.shafarevich_z_construction`.

## The route recorded in this file

Schmidt–Wingberg construct an auxiliary class `z` (their §4, "class form"), which is the six-conjunct
statement `ZSix` defined below (it is also the conclusion of
`Work.SSGRoute.ZDataMup.swZExistsOddSketchH`).  The node's statement is the *Kummer form* of that
class: by the Kummer correspondence for additive locally constant cochains on `G_K`
(`Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst`, proved) the class `z` is
`χ_b` for some `b ∈ Kˣ`, and the node's three clauses are the corresponding conjuncts of `ZSix`
rewritten through `χ_b = z`.  This passage is `sw_odd_kummer_core_of_zSix` below, and it is the
reason the node is *equivalent* to the class form.

The construction of `ZSix` is Schmidt–Wingberg's §4 argument (pp. 14–17):

* the escape recursion `f : ℕ → (Q_m, b_m)` of `Work.SSGRoute.H9.escape_realisation_core_normalised`
  (proved, axiom-clean: the escape oracle with the `v_Q(b) ≡ −1` normalisation, i.e. SW's
  condition (1));
* the shoe box `Work.SSGRoute.pigeonhole_two_eq` on the Frobenius-value vectors
  `Ψ_m(z_m) = (z_m(Frob_{σQ_m}))_σ` (SW's matching `Ψ_N(z_i) = Ψ_N(z_N)`);
* the two-place reciprocity `Work.SSGRoute.ZDataMup.swZTwoPlaceReciprocity` (proved) and the
  Frobenius dictionary `Work.SSGRoute.ZDataMup.localFactor_unramified_eq_frob_pow` (proved) for the
  Hilbert-symbol chain of §4(b), which gives the sibling vanishing at the last escape prime (`hchain`),
  while the sibling vanishing at the earlier escape prime (`hpresc`) is the prescription of
  condition (3);
* the final assembly `Work.SSGRoute.ZSplit.sw_z_exists_odd_of_two_classes` (proved): the class
  `z = z_i + z_N` of the two selected stages satisfies all six conjuncts.
-/

namespace Work.SSGRoute.H9

open _root_.SSGRoute



/-- **The Kummer core follows from its class form.**  By the Kummer correspondence for additive
locally constant cochains on `G_K` (`Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst`,
proved), Schmidt–Wingberg's auxiliary class `z` is the level-`K` Kummer cochain `χ_b` of an element
`b ∈ Kˣ`; the three clauses of the node are then the corresponding conjuncts of `ZSix` rewritten
through `χ_b = z`. -/
theorem sw_odd_kummer_core_of_zSix (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω))
    (y : (Ω ≃ₐ[k] Ω) → ZMod p) (hz : ZSix p k Ω K N S y) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0) := by
  obtain ⟨z, hzadd, hzlc, hzT, hzinf, hzS, hz3⟩ := hz
  obtain ⟨β, hβ⟩ :=
    Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst p k Ω K ζ hζK hζ z hzadd hzlc
  refine ⟨β, ?_, ?_, ?_⟩
  · intro B hB hconj σ hσK hσd
    rw [← hβ σ hσK]
    exact hzT B hB hconj σ hσK hσd
  · intro B hB hS hns σ hσK hσI
    rw [← hβ σ hσK]
    exact hzS B hB hS hns σ hσK hσI
  · intro B hB hS hsplit hram Q hQ hnot τ hτ
    rw [← hβ τ (Subgroup.mem_inf.mp hτ).2]
    refine hz3 B hB hS hsplit ?_ Q hQ hnot τ hτ
    obtain ⟨σ, hσI, hσK, hσne⟩ := hram
    exact ⟨σ, hσI, hσK, fun h0 => hσne (by rw [← hβ σ hσK]; exact h0)⟩

/-- **The odd-`p` Kummer core of Schmidt–Wingberg §4** (the single arithmetic input of the node `Work.SSGRoute.shafarevich_z_construction`, hence of `Work.SSGRoute.shafarevich_existence` and of the Z-side of `Work.SSGRoute.scholz_succ_of_properStage`): for `p ≠ 2`, every additive locally constant datum `y` on `G_K = K.fixingSubgroup` (unramified outside the classes of `S` except where it is not split in `N`, vanishing on the inertia of the places of `S` and on the involutions, and *somewhere* ramified outside them) is the Kummer cochain `χ_b` of an element `b ∈ Kˣ` up to a finite set of new primes, with SW's sharpened condition (b): at every place outside the classes of `S` split in `N` where `χ_b` is ramified, `χ_b` kills the decomposition groups of all the `k`-conjugates that are not `K`-conjugates.  The statement is already on disk (with a `sorry`, character for character) as `Work.SSGRoute.sw_odd_kummer_core` (`Submission/Work/SSGRoute/z_data_mup_odd_of_grunwald.lean:388`) and `Work.SSGRoute.ZDataMup.sw_odd_kummer_core` (`Submission/Work/SSGRoute/ZDataMup/sw_odd_kummer_core.lean`), together with a large amount of proved scaffolding in those two files (in particular `sw_odd_kummer_core_of_unramified`, which disposes of the case in which `y` is unramified outside the classes of `S`, and `kills_localGroup_of_kills_inertia_and_frob`, `clause_six_of_killing_covering_set`).  The route is Grünwald with escape plus the shoebox principle (Schmidt–Wingberg, arXiv:math/9809211, pp. 15–16); the escape input in those files was the *false* `Work.SSGRoute.grunwald_escape_relative`, and the corrected forms are now axiom-clean and must be used instead: `Work.SSGRoute.grunwald_escape_relative_v2` (the `hsplit` repair) and its `L₁ = K` specialisation `Work.GrunwaldEscapeCore.grunwald_escape_correction_L1K` / `Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionL1K`.  The reviewers of this statement flag one proof-side obligation that the earlier scaffolding does not state: the *strengthened escape normalisation* (`v_Q(b) ≡ −1`, i.e. `a_i/a_N = 1`) together with the two-place reciprocity, and the congruence `(z_i)_{P_i} ≡ Frob_{P_i} mod H¹_nr` needed by the §3 chain; `escape_realisation_core` alone does not give it, but `N2v2/` (the proved orthogonality development) and the `L1Korth` files are the natural places to look. -/
theorem sw_odd_kummer_core_proved (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [Fintype (K ≃ₐ[k] K)] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, _root_.SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, _root_.SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (_root_.SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, _root_.SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : _root_.SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ _root_.SSGRoute.IsConjPlace k A B) → ¬ _root_.SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ → y σ = 0)
    (hyram : ∃ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ _root_.SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ ∧ y σ ≠ 0)
    (hyT : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, _root_.SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, _root_.SSGRoute.IsConjPlace k A B) →
      (¬ _root_.SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ _root_.SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, _root_.SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ _root_.SSGRoute.decomp k B →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ) ∧
      (∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ _root_.SSGRoute.IsConjPlace k A B) → ¬ _root_.SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ _root_.SSGRoute.IsConjPlace k A B) → _root_.SSGRoute.IsSplitIn k N B →
        (∃ σ, _root_.SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, _root_.SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ _root_.SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0) := by
  -- The class form of §4 (`Work.SSGRoute.ZDataMup.sw_odd_kummer_core`, character for character the
  -- statement below) followed by the Kummer correspondence `sw_odd_kummer_core_of_zSix` above.
  -- The independent route through `Work.SSGRoute.H9.ZSix_of_histK` (which reduces the class form to
  -- the Kummer-form history `H9.HistK` plus the prescription and the chain at the two escape primes)
  -- is developed in `Submission/Work/SSGRoute/H9/swZSixOfHistK.lean`.
  exact Work.SSGRoute.ZDataMup.sw_odd_kummer_core p hp k Ω K N hKN ζ hζ hζK S hSfin hSdisj hSram
    y hy hyc hyS hyram hyT hy0 hyinf