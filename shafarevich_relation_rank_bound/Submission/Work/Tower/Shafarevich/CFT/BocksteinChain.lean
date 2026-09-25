import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.BocksteinDefs
import Submission.Work.CFT.ClassFormation.Schur.finite_HnZ

/-!
# The homology Bockstein sequence for a finite group

The universal-coefficient (Bockstein) sequence of the coefficient sequence
`0 → ℤ --p→ ℤ → 𝔽_p → 0` of trivial `G`-modules gives, for `n ≥ 2`,

`dim_{𝔽_p} H_n(G, 𝔽_p) = rankP p (H_n(G, ℤ)) + rankP p (H_{n-1}(G, ℤ))`.

This file builds the chain-level short exact sequence of complexes realising it and
uses the long exact homology sequence.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex Finsupp
open scoped TensorProduct

noncomputable section

namespace Work.Tower.Shafarevich.CFT

open Work.CFT.ClassFormation
open Work.CFT.ClassFormation.Schur

/-! ## A general computation: `homologyMap` is `ℤ`-linear -/

/-- `homologyMap` commutes with integer scalar multiplication of chain maps. -/
lemma homologyMap_zsmul_test {C : Type*} [Category* C] [Preadditive C] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (i : ι) [K.HasHomology i]
    [L.HasHomology i] (φ : K ⟶ L) (z : ℤ) :
    HomologicalComplex.homologyMap (z • φ) i = z • HomologicalComplex.homologyMap φ i := by
  let F : (K ⟶ L) →+ (K.homology i ⟶ L.homology i) :=
    { toFun := fun φ => HomologicalComplex.homologyMap φ i
      map_add' := fun φ ψ => HomologicalComplex.homologyMap_add φ ψ i
      map_zero' := HomologicalComplex.homologyMap_zero .. }
  exact map_zsmul F z φ

/-- The map induced on homology by a scalar multiple of the identity. -/
lemma homologyMap_smul_id (K : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ))
    (n : ℕ) (z : ℤ) :
    HomologicalComplex.homologyMap (z • 𝟙 K) n = z • 𝟙 (K.homology n) := by
  rw [homologyMap_zsmul_test, HomologicalComplex.homologyMap_id]

/-! ## The chain level Bockstein short exact sequence -/

variable (p : ℕ) (G : Type) [Group G]

/-- The inhomogeneous chain complex of `G` with trivial integral coefficients. -/
abbrev chainCz : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ) :=
  groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)

/-- The inhomogeneous chain complex of `G` with coefficients `𝔽_p` regarded as a trivial
`ℤ`-representation. -/
abbrev chainCF : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ) :=
  groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod p))

/-- The chain map "reduce modulo `p`" from the integral to the `𝔽_p` chain complex. -/
def redChain : chainCz G ⟶ chainCF p G :=
  groupHomology.chainsMap (A := Rep.trivial ℤ G ℤ) (B := Rep.trivial ℤ G (ZMod p))
    (MonoidHom.id G) (bockG p G)

/-- The chain map "multiply by `p`" on the integral chain complex. -/
def mulChain : chainCz G ⟶ chainCz G :=
  groupHomology.chainsMap (A := Rep.trivial ℤ G ℤ) (B := Rep.trivial ℤ G ℤ)
    (MonoidHom.id G) (bockF p G)

variable [Fact p.Prime]

/-- The degree-`n` component of `redChain` is `Finsupp.mapRange` of reduction mod `p`. -/
lemma chainG_eq_mapRange (n : ℕ) :
    ⇑(((redChain p G).f n)) = Finsupp.mapRange (fun z : ℤ => (z : ZMod p)) (by simp) := by
  ext x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply]
    rw [hf, hg]
    simp only [Finsupp.mapRange_apply, Finsupp.add_apply, Int.cast_add]
  | single a b =>
    rw [redChain, groupHomology.chainsMap_f_single, bockG_hom]
    simp only [MonoidHom.coe_id, Function.id_comp, Finsupp.mapRange_single]

/-- The degree-`n` component of `mulChain` is `Finsupp.mapRange` of multiplication by `p`. -/
lemma chainF_eq_mapRange (n : ℕ) :
    ⇑(((mulChain p G).f n)) = Finsupp.mapRange (fun z : ℤ => p * z) (by simp) := by
  ext x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply]
    rw [hf, hg]
    simp only [Finsupp.mapRange_apply, Finsupp.add_apply]
    ring
  | single a b =>
    rw [mulChain, groupHomology.chainsMap_f_single, bockF_hom]
    simp only [MonoidHom.coe_id, Function.id_comp, Finsupp.mapRange_single]

/-- The degree-`n` component of `mulChain` is multiplication by `p`. -/
lemma mulChain_f_eq (n : ℕ) : (mulChain p G).f n = (p : ℤ) • 𝟙 (chainCz G |>.X n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (((mulChain p G).f n)) y = ((p : ℤ) • 𝟙 ((chainCz G).X n)) y
  rw [chainF_eq_mapRange p G n]
  ext a
  simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, ModuleCat.hom_smul, ModuleCat.hom_id,
    LinearMap.id_apply, LinearMap.smul_apply]
  ring

/-- `mulChain p G` is multiplication by `p` on the integral chain complex. -/
lemma mulChain_eq : mulChain p G = (p : ℤ) • 𝟙 (chainCz G) :=
  HomologicalComplex.hom_ext _ _ (fun n => mulChain_f_eq p G n)

/-- Map induced on homology by `mulChain` is multiplication by `p`. -/
lemma homologyMap_mulChain (n : ℕ) :
    HomologicalComplex.homologyMap (mulChain p G) n
      = (p : ℤ) • 𝟙 ((chainCz G).homology n) := by
  rw [mulChain_eq]
  exact homologyMap_smul_id (chainCz G) n (p : ℤ)

/-- The chain-level Bockstein short complex `0 → ℤ --p→ ℤ --mod p→ 𝔽_p → 0` of trivial
`G`-representations, as a short complex of chain complexes. -/
def bockChainSES : ShortComplex (HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ)) :=
  ShortComplex.mk (mulChain p G) (redChain p G) (by
    rw [mulChain, redChain, ← groupHomology.chainsMap_id_comp, bockF_comp_bockG,
      groupHomology.chainsMap_zero])

/-- The chain-level Bockstein short complex is short exact. -/
theorem bockChainSES_shortExact : (bockChainSES p G).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  have hinj : Function.Injective ⇑((mulChain p G).f n) := by
    rw [chainF_eq_mapRange p G n]
    exact Finsupp.mapRange_injective (fun z : ℤ => p * z) (by simp)
      (fun a b h => mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero) h)
  have hsurj : Function.Surjective ⇑((redChain p G).f n) := by
    rw [chainG_eq_mapRange p G n]
    exact Finsupp.mapRange_surjective (fun z : ℤ => (z : ZMod p)) (by simp)
      ZMod.intCast_surjective
  have hexact : ∀ x : (Fin n → G) →₀ ℤ, (redChain p G).f n x = 0 →
      ∃ y : (Fin n → G) →₀ ℤ, (mulChain p G).f n y = x := by
    intro x hx
    rw [chainG_eq_mapRange p G n] at hx
    have hxa : ∀ a, (x a : ZMod p) = 0 := fun a => by
      have h2 := congrArg (fun f : (Fin n → G) →₀ ZMod p => f a) hx
      simpa [Finsupp.mapRange_apply] using h2
    refine ⟨x.mapRange (fun z : ℤ => z / p) (by simp), ?_⟩
    rw [chainF_eq_mapRange p G n]
    ext a
    rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply]
    have hdvd : (p : ℤ) ∣ x a := (ZMod.intCast_zmod_eq_zero_iff_dvd (x a) p).mp (hxa a)
    have h := Int.ediv_mul_cancel hdvd
    simpa [mul_comm] using h
  have hmono : Mono ((bockChainSES p G).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).f := by
    rw [ModuleCat.mono_iff_injective]
    exact hinj
  have hepi : Epi ((bockChainSES p G).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).g := by
    rw [ModuleCat.epi_iff_surjective]
    exact hsurj
  exact ShortComplex.ShortExact.mk (by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact hexact x hx)

