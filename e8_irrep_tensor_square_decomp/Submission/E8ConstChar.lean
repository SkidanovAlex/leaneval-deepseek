import Submission.E8WInvSub
import Submission.E8FreudenthalGen
import Submission.E8Star
import Submission.E8Rec
import Submission.Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive

/-!
# The characters of the simple constituents of the tensor square

For a simple `U(e₈)`-submodule `S ≤ T N` of the tensor square `T N = (V ⧸ N) ⊗ (V ⧸ N)` with a
primitive generator `x` of dominant weight `Λ = ord40get i`, the function

  `chFun S μ = dim (S ∩ TLwt μ)`

(the multiplicity of the weight `μ` in `S`) satisfies the four hypotheses of
`Submission.E8Character.eq_of_freudenthal` with top weight `Λ`:

* (a) `chFun S Λ ≠ 0` (the primitive generator lies in the top weight space);
* (b) the support bound (`weight_support_of_primitive`);
* (c) `W`-invariance under the dominant conjugate (`E8WInvSub.finrank_inf_TLwt_dc`);
* (d) the Freudenthal recursion (`E8FreudenthalGen.freudenthal_recursion_of_cyclic` at
  `M := ↥S`).

Consequently `chFun S = c * Mnu i` with `c = chFun S Λ ≥ 1`: the candidate characters `Mnu i` of
`Submission/E8Star.lean` are (up to the positive integral scalar `c`) the characters of the actual
constituents, which is the input needed by the isotypic-system route to `ncard = 40`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators TensorProduct

namespace Submission.E8ConstChar

open Submission.E8Tensor Submission.E8TensorBound Submission.VermaWeight
open Submission.E8WeightSpaces Submission.E8Freudenthal
open Submission.E8Weights (SerreE SerreF SerreH)
open Submission.E8Character (posCon posCon_add Bint brk htOf htOf_nonneg)
open Submission.E8Casimir (pR)
open Submission.E8Cert (Mnu)
open Submission.E8Extract (ord40get)
open Submission.WeylReflect (Dominant)
open UniversalEnvelopingAlgebra

variable {N : Submodule U V}

/-! ## The multiplicity function of a submodule -/

/-- `S` regarded as a `ℂ`-submodule of the tensor square.  (Named because the dot-notation
`S.restrictScalars ℂ` is ambiguous in the presence of the `U`-module structure.) -/
abbrev restr {N : Submodule U V} (S : Submodule U (T N)) : Submodule ℂ (T N) :=
  S.restrictScalars ℂ

/-- The multiplicity of the weight `μ` in a `U`-submodule `S` of the tensor square. -/
def chFun (N : Submodule U V) (S : Submodule U (T N)) (μ : Fin 8 → ℤ) : ℚ :=
  (Module.finrank ℂ ↥(restr S ⊓ TLwt N μ) : ℚ)

/-! ## The bridge between `Wt` of the submodule and `TLwt` of the tensor square -/

/-- The `ℂ`-scalar action of a `U(e₈)`-submodule of the tensor square commutes with the
coercion to the tensor square. -/
lemma coe_smul_C (S : Submodule U (T N)) (c : ℂ) (m : ↥S) :
    (((c • m : ↥S) : T N)) = c • (m : T N) := by
  rw [← Submission.Enveloping.algebraMap_smul_eq (R := ℂ) (L := LieAlgebra.e₈ ℂ) c m,
    Submodule.coe_smul,
    Submission.Enveloping.algebraMap_smul_eq (R := ℂ) (L := LieAlgebra.e₈ ℂ) c (m : T N)]

/-- A vector of a submodule lying in the `TLwt`-weight space of the tensor square has the
corresponding `Wt`-weight. -/
lemma mem_Wt_of_mem_TLwt (S : Submodule U (T N)) {μ : Fin 8 → ℤ} {m : ↥S}
    (hm : (m : T N) ∈ TLwt N μ) : m ∈ Submission.E8FreudenthalGen.Wt (M := ↥S) μ := by
  rw [Submission.E8FreudenthalGen.mem_Wt_iff]
  intro j
  refine Subtype.ext ?_
  rw [Submission.E8FreudenthalGen.endM_apply, Submodule.coe_smul, coe_smul_C, iota_smul_eq_deriv]
  exact deriv_h_eq_of_mem_TLwt (N := N) j hm

/-- A vector of a submodule lying in the `Wt`-weight space lies in the `TLwt`-weight space of the
tensor square. -/
lemma mem_TLwt_of_mem_Wt (S : Submodule U (T N)) {μ : Fin 8 → ℤ} {m : ↥S}
    (hm : m ∈ Submission.E8FreudenthalGen.Wt (M := ↥S) μ) : (m : T N) ∈ TLwt N μ := by
  have hx := Submission.E8FreudenthalGen.mem_Wt_iff.mp hm
  refine mem_TLwt_of_deriv_h_eq (N := N) μ (m : T N) ?_
  intro j
  have h3 := congrArg (fun y : ↥S => (y : T N)) (hx j)
  simp only [Submission.E8FreudenthalGen.endM_apply] at h3
  rw [Submodule.coe_smul, iota_smul_eq_deriv] at h3
  exact h3

/-- **The weight space of a submodule, as a subspace of the tensor square.** -/
def wtEquiv (N : Submodule U V) (S : Submodule U (T N)) (μ : Fin 8 → ℤ) :
    ↥(Submission.E8FreudenthalGen.Wt (M := ↥S) μ)
      ≃ₗ[ℂ] ↥(S.restrictScalars ℂ ⊓ TLwt N μ) where
  toFun x := ⟨(x.1 : T N), ⟨x.1.2, mem_TLwt_of_mem_Wt S x.2⟩⟩
  invFun y := ⟨⟨(y.1 : T N),
      (Submodule.restrictScalars_mem ℂ S (y.1 : T N)).mp (Submodule.mem_inf.mp y.2).1⟩,
    mem_Wt_of_mem_TLwt S (Submodule.mem_inf.mp y.2).2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl

/-- The two multiplicity functions agree. -/
theorem chFun_eq_Wt (N : Submodule U V) (S : Submodule U (T N)) (μ : Fin 8 → ℤ) :
    chFun N S μ
      = (Module.finrank ℂ ↥(Submission.E8FreudenthalGen.Wt (M := ↥S) μ) : ℚ) := by
  rw [chFun, ← LinearEquiv.finrank_eq (wtEquiv N S μ)]


/-- The simple-root coordinates of a weight, in the two spellings used in the project. -/
lemma coords_eq (γ : Fin 8 → ℤ) :
    Commons.LinearAlgebra.Matrix.Cartan.coords γ = Submission.E8Character.coords γ := by
  funext i
  simp [Commons.LinearAlgebra.Matrix.Cartan.coords, Submission.E8Character.coords, Matrix.mulVec,
    dotProduct, mul_comm]

/-! ## Hypotheses (a)–(d) of `eq_of_freudenthal` -/

/-- A simple module generated by a non-zero vector. -/
lemma exists_smul_eq_of_simple {S : Submodule U (T N)} [IsSimpleModule U ↥S] {x : T N}
    (hxS : x ∈ S) (hx0 : x ≠ 0) : ∀ m : ↥S, ∃ u : U, u • (⟨x, hxS⟩ : ↥S) = m := by
  intro m
  have hz0 : (⟨x, hxS⟩ : ↥S) ≠ 0 := fun h => hx0 (Subtype.ext_iff.mp h)
  haveI : IsSimpleOrder (Submodule U ↥S) := (isSimpleModule_iff U ↥S).mp ‹IsSimpleModule U ↥S›
  have hspan : Submodule.span U ({⟨x, hxS⟩} : Set ↥S) = ⊤ := by
    rcases eq_bot_or_eq_top (Submodule.span U ({⟨x, hxS⟩} : Set ↥S)) with h | h
    · exfalso
      have h1 : (⟨x, hxS⟩ : ↥S) ∈ (⊥ : Submodule U ↥S) := by
        rw [← h]; exact Submodule.subset_span (Set.mem_singleton _)
      rw [Submodule.mem_bot] at h1
      exact hz0 h1
    · exact h
  have hm : m ∈ Submodule.span U ({⟨x, hxS⟩} : Set ↥S) := by rw [hspan]; trivial
  rw [Submodule.mem_span_singleton] at hm
  obtain ⟨u, hu⟩ := hm
  exact ⟨u, hu ▸ rfl⟩

/-- **The support bound (hypothesis (b))** for the multiplicity function of a simple constituent. -/
theorem chFun_support {N : Submodule U V} {S : Submodule U (T N)} {i : Fin 40} {x : T N}
    (hxS : x ∈ S) (hx0 : x ≠ 0) [IsSimpleModule U ↥S]
    (hprim : ∀ j, deriv (N := N) (SerreE j) x = 0)
    (hwt : ∀ j, deriv (N := N) (SerreH j) x = ((ord40get i j : ℤ) : ℂ) • x)
    {μ : Fin 8 → ℤ} (h : chFun N S μ ≠ 0) :
    ord40get i - μ = 0 ∨
      Submission.E8Character.posCon (ord40get i - μ) := by
  have hne : (restr S ⊓ TLwt N μ : Submodule ℂ (T N)) ≠ ⊥ := by
    intro hbot
    rw [chFun, hbot] at h
    simp at h
  obtain ⟨y, (hy : y ∈ (restr S ⊓ TLwt N μ : Submodule ℂ (T N))), hy0⟩ :=
    (Submodule.ne_bot_iff _).mp hne
  have hyTL : y ∈ TLwt N μ := (Submodule.mem_inf.mp hy).2
  have hyS : y ∈ S :=
    (Submodule.restrictScalars_mem ℂ S y).mp (Submodule.mem_inf.mp hy).1
  have hyW : (⟨y, hyS⟩ : ↥S) ∈ Submission.E8FreudenthalGen.Wt (M := ↥S) μ :=
    mem_Wt_of_mem_TLwt S hyTL
  have hxw : ∀ j, UniversalEnvelopingAlgebra.ι ℂ (SerreH j) • (⟨y, hyS⟩ : ↥S)
      = (((μ j : ℤ)) : ℂ) • (⟨y, hyS⟩ : ↥S) := Submission.E8FreudenthalGen.mem_Wt_iff.mp hyW
  have hE : ∀ j, UniversalEnvelopingAlgebra.ι ℂ (SerreE j) • (⟨x, hxS⟩ : ↥S) = 0 := by
    intro j
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, iota_smul_eq_deriv]
    exact hprim j
  have hH : ∀ j, UniversalEnvelopingAlgebra.ι ℂ (SerreH j) • (⟨x, hxS⟩ : ↥S)
      = (((ord40get i j : ℤ)) : ℂ) • (⟨x, hxS⟩ : ↥S) := by
    intro j
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, coe_smul_C, iota_smul_eq_deriv]
    exact hwt j
  have hsupp := Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive
    (M := ↥S) (⟨x, hxS⟩ : ↥S) (ord40get i)
    (exists_smul_eq_of_simple hxS hx0) hE hH
    (fun hh => hy0 (Subtype.ext_iff.mp hh)) hxw
  refine Or.inr ?_
  intro i
  rw [← coords_eq]
  exact hsupp i

/-- **Hypothesis (c)**: invariance of the multiplicity function under the dominant conjugate. -/
theorem chFun_dc {N : Submodule U V} {S : Submodule U (T N)} (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (ν : Fin 8 → ℤ) :
    chFun N S (Submission.E8Character.dc ν) = chFun N S ν := by
  rw [chFun, chFun, E8WInvSub.finrank_inf_TLwt_dc S hvN hmax ν]

/-- **Hypothesis (d)**: the Freudenthal recursion for the multiplicity function of a simple
constituent. -/
theorem chFun_freudenthal {N : Submodule U V} {S : Submodule U (T N)}
    (hvN : v ∉ N) (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N)
    {i : Fin 40} {x : T N} (hxS : x ∈ S) (hx0 : x ≠ 0) [IsSimpleModule U ↥S]
    (hprim : ∀ j, deriv (N := N) (SerreE j) x = 0)
    (hwt : ∀ j, deriv (N := N) (SerreH j) x = ((ord40get i j : ℤ) : ℂ) • x)
    {ν : Fin 8 → ℤ} (hν : Dominant ν) (hcon : posCon (ord40get i - ν)) :
    (Bint (ord40get i) - Bint ν) * chFun N S ν
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (ord40get i - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * chFun N S (ν + k • pR j) := by
  haveI hfinT : Module.Finite ℂ (T N) := finite_tensor N hvN hmax
  haveI hfinS : Module.Finite ℂ ↥S := Module.Finite.of_injective
    ({ toFun := fun m => (m : T N), map_add' := fun _ _ => rfl,
       map_smul' := fun _ _ => rfl } : ↥S →ₗ[ℂ] T N)
    (fun a b h => Subtype.ext (show (a : T N) = (b : T N) from h))
  have hE : ∀ j, UniversalEnvelopingAlgebra.ι ℂ (SerreE j) • (⟨x, hxS⟩ : ↥S) = 0 := by
    intro j
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, iota_smul_eq_deriv]
    exact hprim j
  have hH : ∀ j, UniversalEnvelopingAlgebra.ι ℂ (SerreH j) • (⟨x, hxS⟩ : ↥S)
      = (((ord40get i j : ℤ)) : ℂ) • (⟨x, hxS⟩ : ↥S) := by
    intro j
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, coe_smul_C, iota_smul_eq_deriv]
    exact hwt j
  have hι : ∀ (y : LieAlgebra.e₈ ℂ) (m : ↥S),
      (UniversalEnvelopingAlgebra.ι ℂ y) • m = ⁅y, m⁆ := fun y m => rfl
  have hc0 : 0 ≤ htOf (ord40get i - ν) := htOf_nonneg hcon
  have h := Submission.E8FreudenthalGen.freudenthal_recursion_of_cyclic (M := ↥S)
    (⟨x, hxS⟩ : ↥S) (ord40get i) (exists_smul_eq_of_simple hxS hx0) hE hH hι ν hc0
  simp only [chFun_eq_Wt N S]
  have hcast : ((Bint (ord40get i) : ℚ) - (Bint ν : ℚ))
      = ((Bint (ord40get i) - Bint ν : ℤ) : ℚ) := (Int.cast_sub ..).symm
  rw [hcast, h]

/-! ## The comparison with the candidate character -/

/-- The multiplicity of the top weight of a simple constituent is non-zero. -/
lemma chFun_top_ne_zero {N : Submodule U V} {S : Submodule U (T N)} {i : Fin 40} {x : T N}
    [Module.Finite ℂ (T N)] (hxS : x ∈ S) (hx0 : x ≠ 0)
    (hwt : ∀ j, deriv (N := N) (SerreH j) x = ((ord40get i j : ℤ) : ℂ) • x) :
    chFun N S (ord40get i) ≠ 0 := by
  have hxL : x ∈ TLwt N (ord40get i) := mem_TLwt_of_deriv_h_eq (N := N) (ord40get i) x hwt
  have hne : (restr S ⊓ TLwt N (ord40get i) : Submodule ℂ (T N)) ≠ ⊥ := by
    intro hbot
    have hmem : x ∈ (⊥ : Submodule ℂ (T N)) := by
      rw [← hbot]
      exact Submodule.mem_inf.mpr ⟨(Submodule.restrictScalars_mem ℂ S x).mpr hxS, hxL⟩
    rw [Submodule.mem_bot] at hmem
    exact hx0 hmem
  haveI : Nontrivial ↥(restr S ⊓ TLwt N (ord40get i) : Submodule ℂ (T N)) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  rw [chFun]
  have hpos : 0 < Module.finrank ℂ ↥(restr S ⊓ TLwt N (ord40get i) : Submodule ℂ (T N)) :=
    Module.finrank_pos (R := ℂ) (M := ↥(restr S ⊓ TLwt N (ord40get i) : Submodule ℂ (T N)))
  exact_mod_cast (ne_of_gt hpos)

/-- The Freudenthal recursion is stable under division by a non-zero constant. -/
lemma freud_div {lam ν : Fin 8 → ℤ} {c : ℚ} {f : (Fin 8 → ℤ) → ℚ} (hc : c ≠ 0)
    (h : (Bint lam - Bint ν) * f ν
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * f (ν + k • pR j)) :
    (Bint lam - Bint ν) * (f ν / c)
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * (f (ν + k • pR j) / c) := by
  have hS : (∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat,
        (brk (ν + k • pR j) j : ℚ) * (f (ν + k • pR j) / c))
      = (∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat,
        (brk (ν + k • pR j) j : ℚ) * f (ν + k • pR j)) / c := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_div_assoc]
  have k1 : (↑(Bint lam) - ↑(Bint ν)) * (f ν / c) = ((↑(Bint lam) - ↑(Bint ν)) * f ν) / c :=
    (mul_div_assoc _ _ _).symm
  have k2 : (2 : ℚ) * ((∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat,
        (brk (ν + k • pR j) j : ℚ) * f (ν + k • pR j)) / c)
      = (2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lam - ν)).toNat,
        (brk (ν + k • pR j) j : ℚ) * f (ν + k • pR j)) / c :=
    (mul_div_assoc _ _ _).symm
  rw [hS, k1, k2, h]

/-- The candidate character, as a rational-valued function. -/
def MnuQ (i : Fin 40) : (Fin 8 → ℤ) → ℚ := fun v => (Mnu i v : ℚ)

lemma MnuQ_top (i : Fin 40) : MnuQ i (ord40get i) = 1 := by
  rw [MnuQ, Submission.E8Star.Mnu_top i]; norm_num

lemma MnuQ_support (i : Fin 40) {v : Fin 8 → ℤ} (h : MnuQ i v ≠ 0) :
    ord40get i - v = 0 ∨ posCon (ord40get i - v) :=
  Submission.E8Star.Mnu_support i (by
    intro h0; exact h (by rw [MnuQ, h0]; norm_num))

lemma MnuQ_dc (i : Fin 40) (v : Fin 8 → ℤ) : MnuQ i (Submission.E8Character.dc v) = MnuQ i v := by
  rw [MnuQ, MnuQ, Submission.E8Star.Mnu_dc i v]

lemma MnuQ_freud (i : Fin 40) {ν : Fin 8 → ℤ} (hν : Dominant ν)
    (hcon : posCon (ord40get i - ν)) :
    (Bint (ord40get i) - Bint ν) * MnuQ i ν
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (ord40get i - ν)).toNat,
          (brk (ν + k • pR j) j : ℚ) * MnuQ i (ν + k • pR j) := by
  have hh := Submission.E8Star.Mnu_freud i hν hcon
  have hcast := congrArg (fun z : ℤ => (z : ℚ)) hh
  push_cast at hcast
  simpa only [MnuQ] using hcast

/-- **The character of a simple constituent is the candidate character `Mnu i`, up to the
positive integral scalar `chFun S (ord40get i)`.** -/
theorem chFun_eq_Mnu {N : Submodule U V} {S : Submodule U (T N)} {i : Fin 40} {x : T N}
    (hvN : v ∉ N) (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N)
    (hxS : x ∈ S) (hx0 : x ≠ 0) [IsSimpleModule U ↥S]
    (hprim : ∀ j, deriv (N := N) (SerreE j) x = 0)
    (hwt : ∀ j, deriv (N := N) (SerreH j) x = ((ord40get i j : ℤ) : ℂ) • x)
    (μ : Fin 8 → ℤ) :
    chFun N S μ = chFun N S (ord40get i) * Mnu i μ := by
  have hlam : Dominant (ord40get i) := Submission.E8Star.ord40_dom i
  haveI hfinT : Module.Finite ℂ (T N) := finite_tensor N hvN hmax
  have hc : chFun N S (ord40get i) ≠ 0 := chFun_top_ne_zero hxS hx0 hwt
  have hmain := Submission.E8Character.eq_of_freudenthal (lam := ord40get i) hlam
    (m := MnuQ i) (m' := fun μ => chFun N S μ / chFun N S (ord40get i))
    (MnuQ_top i)
    (by rw [div_self hc])
    (fun v hv => MnuQ_support i hv)
    (fun v hv => chFun_support hxS hx0 hprim hwt (fun h0 => hv (by rw [h0, zero_div])))
    (MnuQ_dc i)
    (fun v => by rw [chFun_dc hvN hmax v])
    (fun ν hν _ hcon => MnuQ_freud i hν hcon)
    (fun ν hν _ hcon => freud_div hc (chFun_freudenthal hvN hmax hxS hx0 hprim hwt hν hcon))
  have this : (Mnu i μ : ℚ) = chFun N S μ / chFun N S (ord40get i) := hmain μ
  rw [eq_div_iff hc] at this
  rw [← this, mul_comm]

end Submission.E8ConstChar
