/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epimorphisms out of a von Neumann regular ring are surjective (universe-general)

The classical theorem of Stenström (*Rings of quotients*, XI.1.4) and Gardner
(*Epimorphisms of regular rings*, Comment. Math. Univ. Carolinae **16** (1975), Theorem 1.6):
an epic ring homomorphism `f : R →+* S` whose source `R` is von Neumann regular is surjective.
Equivalently, a ring homomorphism is epic if and only if it cannot be factored through a proper
subring of its target when the source is von Neumann regular.

The workspace already contains this theorem at universe `0`
(`Submission.Work.ORHughesFree.Section3.surjective_of_isEpic_vnRegular`).  The diagonal
`∗`-regular closure appearing in the uniqueness of epic `∗`-regular envelopes
([JZLA20, Theorem 2.9]) lives in `U₁ × U₂` with `Uᵢ : Type u` for an arbitrary fixed universe
`u`, so the theorem is needed at `Type u`.  This file supplies a **self-contained** version: it
repeats, at `Type u`, the three ingredients of the proof

* `matrixAssembly` — Mazet matrix assembly (from the Mazet data to a matrix presentation);
* the `Mazet` development and `mazetPresentation` — the Isbell--Silver--Mazet presentation of an
  arbitrary element `d : S` from the tensor relation `s ⊗ 1 = 1 ⊗ s`;
* `mul_eq_of_isEpic`, `tmul_eq_of_isEpic` (Silver's step) and `exists_preimage_of_matrix_eq`
  (the von Neumann regular step);

and then assembles them into `stenstromVnRegularU`.

The proofs are the proofs of the universe-`0` originals, transported verbatim; only the universe
binders change.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.BalancedTensor
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.Section3.EpicSurjectiveUniverse

open Matrix
open Work.ORHughesFree
open Work.ORHughesFree.Epic (BalancedTensor)
open scoped TensorProduct

/-! ## Mazet matrix assembly -/


open Matrix

/-- **Mazet matrix assembly.**  Given the Mazet data attached to a tensor relation
(`∑_s s * f (a μ s) + f (astar μ) = 0`, `t s = ∑_μ f (a μ s) * z μ`, `t s ∈ f(R)`,
`d = -∑_μ f (astar μ) * z μ`), the element `d` is the `(0,0)` entry of a product
`X * f(P) * Y` of matrices over `S` with `X * f(P)` a row over `f(R)` and `f(P) * Y` a column
over `f(R)`.

The construction: let `U` be the finite set of `s : S` on which some `a μ` is supported, index
the matrices by `U ⊕ Fin m` (via an enumeration of that finite type), and set

* `X 0 (inl i) = i`, `X 0 (inr μ) = 0`,
* `P (inl i) (inr μ) = a μ i` and `P = 0` on all other blocks,
* `Y (inr μ) 0 = z μ`, `Y (inl i) 0 = 0`.

Then `X * f(P) = [-∑_i i f (a μ i)]_μ = [-f (astar μ)]_μ` by the relation, and
`f(P) * Y = [∑_μ f (a μ i) z μ]_i = [t i]_i` lies over `f(R)` by `hfin`; the `(0,0)` entry of
the product is `-∑_μ f (astar μ) z μ = d`. -/
theorem matrixAssembly {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (d : S) (m : ℕ)
    (a : Fin m → S →₀ R) (astar : Fin m → R) (z : Fin m → S) (t : S →₀ S)
    (hrel : ∀ mu, (a mu).sum (fun s r => s * f r) + f (astar mu) = 0)
    (hrow : ∀ s, t s = ∑ mu, f (a mu s) * z mu)
    (hfin : ∀ s, t s ∈ Set.range f)
    (hstar : d = - ∑ mu, f (astar mu) * z mu) :
    ∃ (n : ℕ) (X : Matrix (Fin 1) (Fin n) S) (P : Matrix (Fin n) (Fin n) R)
      (Y : Matrix (Fin n) (Fin 1) S),
      (∃ P' : Matrix (Fin 1) (Fin n) R, X * P.map f = P'.map f) ∧
      (∃ Q' : Matrix (Fin n) (Fin 1) R, P.map f * Y = Q'.map f) ∧
      d = (X * P.map f * Y) 0 0 := by
  classical
  -- The finite set of `s : S` on which one of the `a μ` is supported.
  set U : Finset S := Finset.univ.biUnion (fun μ : Fin m => (a μ).support) with hU
  have hUmem : ∀ s : S, s ∈ U ↔ ∃ μ : Fin m, a μ s ≠ 0 := by
    intro s
    rw [hU, Finset.mem_biUnion]
    exact ⟨fun ⟨μ, _, hs⟩ => ⟨μ, Finsupp.mem_support_iff.mp hs⟩,
      fun ⟨μ, hμ⟩ => ⟨μ, Finset.mem_univ μ, Finsupp.mem_support_iff.mpr hμ⟩⟩
  -- An enumeration of the double index set `↥U ⊕ Fin m`.
  set e : (↥U ⊕ Fin m) ≃ Fin (U.card + m) :=
    (Equiv.sumCongr (Finset.equivFin U) (Equiv.refl (Fin m))).trans finSumFinEquiv with he
  -- The relation `∑ i ∈ U, i * f (a μ i) = - f (astar μ)`.
  have hsum : ∀ μ : Fin m, (∑ i : ↥U, (i : S) * f (a μ (i : S))) = - f (astar μ) := by
    intro μ
    have hsub : (a μ).support ⊆ U :=
      fun s hs => (hUmem s).mpr ⟨μ, Finsupp.mem_support_iff.mp hs⟩
    rw [show (∑ i : ↥U, (i : S) * f (a μ (i : S))) = ∑ x ∈ U, x * f (a μ x) from by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach U (fun x => x * f (a μ x))]
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      have h0 : a μ x = 0 := by
        by_contra hne
        exact hx (Finsupp.mem_support_iff.mpr hne)
      simp [h0])]
    exact eq_neg_of_add_eq_zero_left (hrel μ)
  -- The matrices.
  let X : Matrix (Fin 1) (Fin (U.card + m)) S :=
    fun _ k => Sum.elim (fun i : ↥U => (i : S)) (fun _ : Fin m => (0 : S)) (e.symm k)
  let P : Matrix (Fin (U.card + m)) (Fin (U.card + m)) R :=
    fun k l => Sum.elim
      (fun i : ↥U => Sum.elim (fun _ : ↥U => (0 : R)) (fun μ : Fin m => a μ (i : S))
        (e.symm l))
      (fun _ : Fin m => (0 : R)) (e.symm k)
  let Y : Matrix (Fin (U.card + m)) (Fin 1) S :=
    fun k _ => Sum.elim (fun _ : ↥U => (0 : S)) (fun μ : Fin m => z μ) (e.symm k)
  let P' : Matrix (Fin 1) (Fin (U.card + m)) R :=
    fun _ l => Sum.elim (fun _ : ↥U => (0 : R)) (fun μ : Fin m => - astar μ) (e.symm l)
  let y : ↥U → R := fun i => Classical.choose (hfin (i : S))
  have hy : ∀ i : ↥U, f (y i) = t (i : S) := fun i => Classical.choose_spec (hfin (i : S))
  let Q' : Matrix (Fin (U.card + m)) (Fin 1) R :=
    fun k _ => Sum.elim (fun i : ↥U => y i) (fun _ : Fin m => (0 : R)) (e.symm k)
  -- `X * f(P)` is the row `(- f (astar μ))_μ` over `f(R)`.
  have h1 : X * P.map f = P'.map f := by
    ext i l
    fin_cases i
    obtain ⟨k, rfl⟩ := e.surjective l
    rcases k with j | μ
    · rw [Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
      simp only [Matrix.map_apply]
      simp [X, P, P']
    · rw [Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
      simp only [Matrix.map_apply]
      simp only [X, P, P', Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
      rw [hsum μ]
      simp [map_neg]
  -- `f(P) * Y` is the column `(t i)_i` over `f(R)`.
  have h2 : P.map f * Y = Q'.map f := by
    ext k i
    fin_cases i
    obtain ⟨x, rfl⟩ := e.surjective k
    rcases x with j | ν
    · rw [Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
      simp only [Matrix.map_apply]
      simp only [X, P, Y, Q', Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
      rw [← hrow (j : S), hy j]
      simp
    · rw [Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
      simp only [Matrix.map_apply]
      simp [X, P, Y, Q']
  refine ⟨U.card + m, X, P, Y, ⟨P', h1⟩, ⟨Q', h2⟩, ?_⟩
  rw [h1, Matrix.mul_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp only [Matrix.map_apply]
  simp only [X, P', Y, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hstar]
  simp [map_neg, neg_mul, Finset.sum_neg_distrib]


/-! ## Mazet's presentation (Isbell--Silver--Mazet) -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Work.ORHughesFree.Epic (BalancedTensor)
open scoped TensorProduct

/-!
# Mazet's presentation for epic ring homomorphisms

Let `f : R →+* S` be a ring homomorphism such that `s ⊗ 1 = 1 ⊗ s` in `S ⊗[R] S` for every
`s : S` (the Isbell–Silver–Mazet criterion for `f` being an epimorphism).  We prove that then
every `d : S` has a *Mazet presentation*: `d = X · f(P) · Y` for matrices `X` over `S`,
`P` over `R` and `Y` over `S`, where `X · f(P)` is a row over `f(R)` and `f(P) · Y` is a
column over `f(R)`.

The mathematical content is Mazet's lemma (cf. P. Mazet, *Caractérisation des épimorphismes
par relations et générateurs*, Séminaire Samuel 1967/68): from a tensor relation in
`S ⊗[R] S` one extracts linear relations over `R` realising the elements involved through the
generators `s ⊗ -` (`t_s = ∑_μ f (a μ s) * z μ`, `∑_s s * f (a μ s) + f (astar μ) = 0`).

The formalisation goes through the `R`-balanced tensor product `BalancedTensor f` of
`Submission.Work.ORHughesFree.Epic.BalancedTensor`.  The subgroup `Rel f` below is the set of
elements of `(S →₀ S) × S` (the free `R`-module on the generators `s ∈ S` tensored with `S`,
together with one extra generator `★` mapping to `1 ∈ S`) which admit the Mazet-type
presentation.  The key exactness statement is `Mazet.theta_mem`: the kernel of the canonical
map `θ : (S →₀ S) × S → BalancedTensor f` is contained in `Rel f`.
-/

namespace Mazet

variable {R S : Type u} [Ring R] [Ring S]

/-! ### The elementary relation attached to `c : S →₀ R` and `y : S` -/

/-- `relElem f c y` is the finitely supported function `s ↦ f (c s) * y`. -/
noncomputable def relElem (f : R →+* S) (c : S →₀ R) (y : S) : S →₀ S :=
  (c.mapRange f (map_zero f)).mapRange (fun x => x * y) (zero_mul y)

lemma relElem_apply (f : R →+* S) (c : S →₀ R) (y : S) (a : S) :
    relElem f c y a = f (c a) * y := by
  classical
  simp [relElem, Finsupp.mapRange_apply]

lemma relElem_single (f : R →+* S) (a : S) (r : R) (y : S) :
    relElem f (Finsupp.single a r) y = Finsupp.single a (f r * y) := by
  classical
  ext b
  rw [relElem_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : a = b <;> simp [h]

lemma relElem_sub (f : R →+* S) (c c' : S →₀ R) (y : S) :
    relElem f (c - c') y = relElem f c y - relElem f c' y := by
  classical
  ext a
  rw [Finsupp.sub_apply, relElem_apply, relElem_apply, relElem_apply, Finsupp.sub_apply,
    map_sub, sub_mul]

/-! ### The subgroup `Rel f` of Mazet presentations -/

/-- The (additive) subgroup of `(S →₀ S) × S` consisting of the elements which "admit a Mazet
presentation": `x = (z, w)` lies in `Rel f` if there are finitely many columns `μ`, a family
`a μ : S →₀ R` (finitely supported), scalars `astar μ ∈ R` and elements `z μ ∈ S` with

* `∑_s s * f (a μ s) + f (astar μ) = 0` (the relations),
* `z s = ∑_μ f (a μ s) * z μ` for all `s`,
* `w = ∑_μ f (astar μ) * z μ`.

The second factor `S` of the product models the extra generator `★ ↦ 1` of Mazet's
argument. -/
noncomputable def Rel (f : R →+* S) : AddSubgroup ((S →₀ S) × S) where
  carrier := {x | ∃ (m : ℕ) (a : Fin m → S →₀ R) (astar : Fin m → R) (z : Fin m → S),
      (∀ μ, (a μ).sum (fun a r => a * f r) + f (astar μ) = 0) ∧
      (∀ b, x.1 b = ∑ μ, f (a μ b) * z μ) ∧
      (x.2 = ∑ μ, f (astar μ) * z μ)}
  zero_mem' := by
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · intro μ; exact μ.elim0
    · intro b; simp
    · simp
  add_mem' := by
    rintro x y ⟨m, a, astar, z, hrel, hx1, hx2⟩ ⟨m', a', astar', z', hrel', hy1, hy2⟩
    have key : ∀ b : S, (∑ μ : Fin (m+m'), f ((Fin.append a a' μ) b) * Fin.append z z' μ)
        = (∑ i : Fin m, f (a i b) * z i) + (∑ i : Fin m', f (a' i b) * z' i) := by
      intro b
      rw [Fin.sum_univ_add]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left, Fin.append_left]
      · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right, Fin.append_right]
    have key2 : (∑ μ : Fin (m+m'), f ((Fin.append astar astar') μ) * Fin.append z z' μ)
        = (∑ i : Fin m, f (astar i) * z i) + (∑ i : Fin m', f (astar' i) * z' i) := by
      rw [Fin.sum_univ_add]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left, Fin.append_left]
      · exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right, Fin.append_right]
    refine ⟨m + m', Fin.append a a', Fin.append astar astar', Fin.append z z', ?_, ?_, ?_⟩
    · intro μ
      refine Fin.addCases (motive := fun μ => ((Fin.append a a') μ).sum (fun a r => a * f r)
        + f ((Fin.append astar astar') μ) = 0) (fun i => ?_) (fun i => ?_) μ
      · rw [Fin.append_left, Fin.append_left]; exact hrel i
      · rw [Fin.append_right, Fin.append_right]; exact hrel' i
    · intro b
      rw [Prod.fst_add, Finsupp.add_apply, hx1 b, hy1 b, key b]
    · rw [Prod.snd_add, hx2, hy2, key2]
  neg_mem' := by
    rintro x ⟨m, a, astar, z, hrel, hx1, hx2⟩
    refine ⟨m, a, astar, fun μ => -z μ, ?_, ?_, ?_⟩
    · intro μ; exact hrel μ
    · intro b
      rw [Prod.fst_neg, Finsupp.neg_apply, hx1 b, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_neg]
    · rw [Prod.snd_neg, hx2, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_neg]

/-- The elementary elements of `Rel f`: from a relation `c : S →₀ R` (with `∑_s s * f (c s) = 0`)
and an element `y : S` one obtains `(relElem f c y, 0) ∈ Rel f`. -/
lemma Rel_of_relElem (f : R →+* S) (c : S →₀ R) (y : S)
    (hc : c.sum (fun a r => a * f r) = 0) : (relElem f c y, 0) ∈ Rel f := by
  refine ⟨1, fun _ => c, fun _ => 0, fun _ => y, ?_, ?_, ?_⟩
  · intro μ; simpa using hc
  · intro b; rw [relElem_apply]; simp
  · simp

/-- The "additivity in the first variable" defect lies in `Rel f`. -/
lemma Rel_defect_add (f : R →+* S) (s s' t : S) :
    (Finsupp.single (s + s') t - Finsupp.single s t - Finsupp.single s' t, 0) ∈ Rel f := by
  have hsub : ∀ (a : S) (b₁ b₂ : R),
      (fun a r => a * f r) a (b₁ - b₂) = (fun a r => a * f r) a b₁ - (fun a r => a * f r) a b₂ := by
    intro a b₁ b₂; simp only; rw [map_sub, mul_sub]
  have hc : (Finsupp.single (s + s') (1 : R) - Finsupp.single s (1 : R)
      - Finsupp.single s' (1 : R)).sum (fun a r => a * f r) = 0 := by
    rw [Finsupp.sum_sub_index hsub, Finsupp.sum_sub_index hsub,
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp)]
    simp
  have h := Rel_of_relElem f _ t hc
  simp only [relElem_sub, relElem_single, map_one, one_mul] at h
  exact h

/-- The "integer scaling in the first variable" defect lies in `Rel f`. -/
lemma Rel_defect_smul (f : R →+* S) (s t : S) (n : ℤ) :
    (Finsupp.single (n • s) t - Finsupp.single s (n • t), 0) ∈ Rel f := by
  have hsub : ∀ (a : S) (b₁ b₂ : R),
      (fun a r => a * f r) a (b₁ - b₂) = (fun a r => a * f r) a b₁ - (fun a r => a * f r) a b₂ := by
    intro a b₁ b₂; simp only; rw [map_sub, mul_sub]
  have hc : (Finsupp.single (n • s) (1 : R) - Finsupp.single s (↑n : R)).sum
      (fun a r => a * f r) = 0 := by
    rw [Finsupp.sum_sub_index hsub, Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp)]
    simp [map_intCast, zsmul_eq_mul, Int.cast_comm]
  have h := Rel_of_relElem f _ t hc
  simp only [relElem_sub, relElem_single, map_one, one_mul, map_intCast] at h
  rw [← zsmul_eq_mul] at h
  exact h

/-- The "balance" defect lies in `Rel f`. -/
lemma Rel_defect_balance (f : R →+* S) (s t : S) (r : R) :
    (Finsupp.single (s * f r) t - Finsupp.single s (f r * t), 0) ∈ Rel f := by
  have hsub : ∀ (a : S) (b₁ b₂ : R),
      (fun a r => a * f r) a (b₁ - b₂) = (fun a r => a * f r) a b₁ - (fun a r => a * f r) a b₂ := by
    intro a b₁ b₂; simp only; rw [map_sub, mul_sub]
  have hc : (Finsupp.single (s * f r) (1 : R) - Finsupp.single s r).sum
      (fun a r => a * f r) = 0 := by
    rw [Finsupp.sum_sub_index hsub, Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp)]
    simp
  have h := Rel_of_relElem f _ t hc
  simp only [relElem_sub, relElem_single, map_one, one_mul] at h
  exact h

/-- The extra generator `★` of Mazet's argument maps to `1 ∈ S`. -/
lemma Rel_single_one (f : R →+* S) (t : S) :
    (Finsupp.single (1 : S) t, -t) ∈ Rel f := by
  refine ⟨1, fun _ => Finsupp.single (1 : S) (1 : R), fun _ => -1, fun _ => t, ?_, ?_, ?_⟩
  · intro μ
    rw [Finsupp.sum_single_index (by simp), map_one, mul_one, map_neg, map_one]
    abel
  · intro b
    simp only [Fin.sum_univ_one]
    rw [← relElem_apply, relElem_single, map_one, one_mul]
  · simp only [Fin.sum_univ_one]
    rw [map_neg, map_one, neg_one_mul]

/-! ### The canonical map `θ : (S →₀ S) × S → BalancedTensor f` -/

/-- `tmul f a -` vanishes at `0`. -/
theorem bt_tmul_zero_right (f : R →+* S) (a : S) : BalancedTensor.tmul f a 0 = 0 := by
  show BalancedTensor.mk f (a ⊗ₜ[ℤ] (0 : S)) = 0
  rw [TensorProduct.tmul_zero, map_zero]

/-- `tmul f - t` vanishes at `0`. -/
theorem bt_tmul_zero_left (f : R →+* S) (t : S) : BalancedTensor.tmul f 0 t = 0 := by
  show BalancedTensor.mk f ((0 : S) ⊗ₜ[ℤ] t) = 0
  rw [TensorProduct.zero_tmul, map_zero]

/-- The additive homomorphism `v ↦ tmul f a v`. -/
noncomputable def tmulHom (f : R →+* S) (a : S) : S →+ BalancedTensor f where
  toFun v := BalancedTensor.tmul f a v
  map_zero' := bt_tmul_zero_right f a
  map_add' := fun v v' => BalancedTensor.tmul_add_right f a v v'

/-- The canonical map on the free part `S →₀ S`: the generators `s ↦ s ⊗ -`. -/
noncomputable def theta1 (f : R →+* S) : (S →₀ S) →+ BalancedTensor f :=
  Finsupp.liftAddHom (fun a => tmulHom f a)

lemma theta1_apply (f : R →+* S) (z : S →₀ S) :
    theta1 f z = z.sum (fun a v => BalancedTensor.tmul f a v) := by
  rw [theta1, Finsupp.liftAddHom_apply]
  rfl

/-- The extra generator `★ ↦ 1`. -/
noncomputable def theta2 (f : R →+* S) : S →+ BalancedTensor f := tmulHom f 1

/-- The canonical map `θ : (S →₀ S) × S → BalancedTensor f`, `(z, w) ↦ ∑_s s ⊗ z_s + 1 ⊗ w`. -/
noncomputable def theta (f : R →+* S) : ((S →₀ S) × S) →+ BalancedTensor f :=
  (theta1 f).comp (AddMonoidHom.fst _ _) + (theta2 f).comp (AddMonoidHom.snd _ _)

lemma theta_apply (f : R →+* S) (x : (S →₀ S) × S) :
    theta f x = theta1 f x.1 + BalancedTensor.tmul f 1 x.2 := rfl

/-! ### The inverse map on `((S →₀ S) × S) ⧸ Rel f` -/

/-- Pushforward of a finsupp sum along an additive map. -/
lemma map_finsupp_sum {A N N' : Type u} [AddCommMonoid A] [AddCommMonoid N] [AddCommMonoid N']
    (φ : N → N') (h0 : φ 0 = 0) (hadd : ∀ x y : N, φ (x + y) = φ x + φ y)
    (z : S →₀ A) (g : S → A → N) : φ (z.sum g) = z.sum (fun a v => φ (g a v)) := by
  rw [Finsupp.sum, Finsupp.sum]
  exact map_sum (⟨⟨φ, h0⟩, hadd⟩ : N →+ N') (fun a => g a (z a)) z.support

/-- The additive homomorphism `z ↦ (z, 0)`. -/
noncomputable def inlHom : (S →₀ S) →+ ((S →₀ S) × S) where
  toFun z := (z, 0)
  map_zero' := rfl
  map_add' z z' := by rw [Prod.mk_add_mk, add_zero]

/-- The bilinear map `(s, t) ↦ (single s t, 0)` modulo `Rel f`. -/
noncomputable def beta (f : R →+* S) : S →ₗ[ℤ] S →ₗ[ℤ] ((S →₀ S) × S) ⧸ Rel f :=
  LinearMap.mk₂ ℤ (fun s t => QuotientAddGroup.mk' (Rel f) (Finsupp.single s t, (0 : S)))
    (fun s s' t => by
      rw [← map_add]
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      have h := Rel_defect_add f s s' t
      simpa [Prod.mk_add_mk, Prod.mk_sub_mk, sub_sub] using h)
    (fun n s t => by
      rw [← map_zsmul]
      rw [Prod.smul_mk, smul_zero, Finsupp.smul_single]
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      have h := Rel_defect_smul f s t n
      simpa [Prod.mk_sub_mk] using h)
    (fun s t t' => by
      have key : ((Finsupp.single s t + Finsupp.single s t', (0:S)) : (S →₀ S) × S)
          = (Finsupp.single s t, (0:S)) + (Finsupp.single s t', (0:S)) := by
        rw [Prod.mk_add_mk, add_zero]
      rw [Finsupp.single_add, key, map_add])
    (fun n s t => by
      rw [← map_zsmul]
      rw [Prod.smul_mk, smul_zero, Finsupp.smul_single])

lemma beta_apply (f : R →+* S) (s t : S) :
    beta f s t = QuotientAddGroup.mk' (Rel f) (Finsupp.single s t, (0 : S)) := rfl

/-- The inverse of `θ` on the quotient: `tmul f s t ↦ (single s t, 0)`. -/
noncomputable def phi (f : R →+* S) : BalancedTensor f →+ ((S →₀ S) × S) ⧸ Rel f :=
  BalancedTensor.lift f (beta f) (fun s t r => by
    rw [beta_apply f (s * f r) t, beta_apply f s (f r * t)]
    refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
    have hh := Rel_defect_balance f s t r
    simpa [Prod.mk_sub_mk] using hh)

lemma phi_tmul (f : R →+* S) (s t : S) :
    phi f (BalancedTensor.tmul f s t)
      = QuotientAddGroup.mk' (Rel f) (Finsupp.single s t, (0 : S)) := by
  rw [phi, BalancedTensor.lift_tmul, beta_apply]

/-- `phi` is a left inverse of `θ`: the kernel of `θ` is contained in `Rel f`. -/
lemma theta_mem (f : R →+* S) (x : (S →₀ S) × S) (hx : theta f x = 0) : x ∈ Rel f := by
  have h2 : phi f (theta f x) = QuotientAddGroup.mk' (Rel f) x := by
    have hA : ∀ z : S →₀ S, phi f (theta1 f z) = QuotientAddGroup.mk' (Rel f) (inlHom z) := by
      intro z
      rw [theta1_apply]
      rw [map_finsupp_sum (phi f ·) (map_zero (phi f)) (map_add (phi f)) z
        (fun s v => BalancedTensor.tmul f s v)]
      have hsum : z.sum (fun s v => inlHom (Finsupp.single s v)) = inlHom z := by
        rw [← map_finsupp_sum (inlHom ·) (map_zero inlHom) (map_add inlHom) z
          (fun s v => Finsupp.single s v), Finsupp.sum_single]
      rw [← hsum, map_finsupp_sum (QuotientAddGroup.mk' (Rel f) ·)
        (map_zero (QuotientAddGroup.mk' (Rel f))) (map_add (QuotientAddGroup.mk' (Rel f))) z
        (fun s v => inlHom (Finsupp.single s v))]
      exact Finsupp.sum_congr fun s _ => by rw [phi_tmul]; rfl
    have hB : phi f (BalancedTensor.tmul f 1 x.2)
        = QuotientAddGroup.mk' (Rel f) ((0 : S →₀ S), x.2) := by
      rw [phi_tmul]
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      simpa [Prod.mk_sub_mk] using Rel_single_one f x.2
    rw [theta_apply, map_add, hA, hB, ← map_add]
    congr 1
    apply Prod.ext <;> simp [inlHom]
  have h1 : phi f (theta f x) = 0 := by rw [hx, map_zero]
  rw [h2] at h1
  have hker := (QuotientAddGroup.mk' (Rel f)).mem_ker.mpr h1
  rwa [QuotientAddGroup.ker_mk'] at hker

/-- **Mazet's lemma.**  If `∑_s tmul f s (t s) + tmul f 1 ts = 0` in `S ⊗[R] S`, then `t` and
`ts` admit a Mazet presentation: there are finitely many columns `μ`, finitely supported
families `a μ : S →₀ R`, scalars `astar μ ∈ R` and elements `z μ ∈ S` with the stated
relations. -/
theorem syzygy (f : R →+* S) {t : S →₀ S} {ts : S} (h : theta f (t, ts) = 0) :
    ∃ (m : ℕ) (a : Fin m → S →₀ R) (astar : Fin m → R) (z : Fin m → S),
      (∀ μ, (a μ).sum (fun s r => s * f r) + f (astar μ) = 0) ∧
      (∀ s, t s = ∑ μ, f (a μ s) * z μ) ∧
      (ts = ∑ μ, f (astar μ) * z μ) := by
  have hmem : (t, ts) ∈ Rel f := theta_mem f (t, ts) h
  obtain ⟨m, a, astar, z, h1, h2, h3⟩ := hmem
  exact ⟨m, a, astar, z, h1, h2, h3⟩

end Mazet

theorem mazetPresentation {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (h : ∀ s : S, Work.ORHughesFree.Epic.BalancedTensor.tmul f s 1
        = Work.ORHughesFree.Epic.BalancedTensor.tmul f 1 s) (d : S) :
    ∃ (n : ℕ) (X : Matrix (Fin 1) (Fin n) S) (P : Matrix (Fin n) (Fin n) R)
      (Y : Matrix (Fin n) (Fin 1) S),
      (∃ P' : Matrix (Fin 1) (Fin n) R, X * P.map f = P'.map f) ∧
      (∃ Q' : Matrix (Fin n) (Fin 1) R, P.map f * Y = Q'.map f) ∧
      d = (X * P.map f * Y) 0 0 := by
  classical
  -- the tensor relation `d ⊗ 1 - 1 ⊗ d = 0`
  have hrel : Mazet.theta f (Finsupp.single d (1 : S), -d) = 0 := by
    rw [Mazet.theta_apply, Mazet.theta1_apply]
    rw [Finsupp.sum_single_index (Mazet.bt_tmul_zero_right f d)]
    have hneg : BalancedTensor.tmul f 1 (-d) = - BalancedTensor.tmul f 1 d := by
      have h0 : BalancedTensor.tmul f 1 (-d + d) = 0 := by
        rw [neg_add_cancel]; exact Mazet.bt_tmul_zero_right f 1
      rw [BalancedTensor.tmul_add_right] at h0
      exact eq_neg_of_add_eq_zero_left h0
    rw [hneg, h d, add_neg_cancel]
  obtain ⟨m, a, astar, z, h1, h2, h3⟩ := Mazet.syzygy f hrel
  exact matrixAssembly f d m a astar z (Finsupp.single d (1 : S)) h1 h2 (by
    intro s
    rw [Finsupp.single_apply]
    by_cases hs : d = s
    · rw [if_pos hs]; exact ⟨1, map_one f⟩
    · rw [if_neg hs]; exact ⟨0, map_zero f⟩) (by
      rw [← h3, neg_neg])


/-! ## Silver's step, the von Neumann regular step, and the assembly -/


open Work.ORHughesFree
open Work.ORHughesFree.Epic

/-!
# Epimorphisms out of a von Neumann regular ring are surjective

The classical theorem (Stenström, *Rings of quotients*, XI.1.4; Gardner, *Epimorphisms of
regular rings*) that an epic ring homomorphism `f : R →+* S` with `R` von Neumann regular is
surjective.

The proof has three ingredients.

* **Silver's step.**  If `f` is epic and `m` is an element of an `(S,S)`-bimodule fixed by the
  image of `R`, then `m` is fixed by all of `S`.  This is proved with the trivial extension
  `S ⋉ M` of `M` (Mathlib's `TrivSqZeroExt`): the two ring homomorphisms
  `s ↦ (s, 0)` and `s ↦ (s, s • m - m • s)` agree on `f(R)`, hence on all of `S` by epicity.
* **The Mazet presentation** (Isbell–Silver–Mazet): every `d : S` can be written as
  `d = X · f(P) · Y` with `X` a row over `S`, `P` a square matrix over `R`, `Y` a column over
  `S`, and `X · f(P)`, `f(P) · Y` matrices over `f(R)`.  This is recorded in the module
  `Submission.Work.ORHughesFree.Section3.mazetPresentation`, whose hypothesis is exactly Silver's
  conclusion applied to `m = 1 ⊗ 1` in the `R`-balanced tensor product `S ⊗[R] S`.
* **The von Neumann regular step.**  Since `Mat n R` is von Neumann regular, `P = P T P` for
  some `T`, so `d = (X f(P)) · f(T) · (f(P) Y)`, a `1 × 1` matrix over `f(R)`; hence `d = f r`.
-/

/-- **Silver's step.**  Let `M` be an `(S,S)`-bimodule and `m ∈ M` an element fixed by the image
of `f : R →+* S` (`f r • m = m • f r`).  If `f` is epic then `d • m = m • d` for every `d : S`.

The proof uses the trivial extension `S ⋉ M`: `s ↦ (s, 0)` and `s ↦ (s, s • m - m • s)` are ring
homomorphisms `S → TrivSqZeroExt S M` which agree on `f(R)`, hence are equal by epicity. -/
theorem mul_eq_of_isEpic {R S M : Type u} [Ring R] [Ring S] [AddCommGroup M]
    [Module S M] [Module Sᵐᵒᵖ M] [SMulCommClass S Sᵐᵒᵖ M]
    (f : R →+* S) (hf : IsEpic f) (m : M)
    (hm : ∀ r : R, f r • m = MulOpposite.op (f r) • m) (d : S) :
    d • m = MulOpposite.op d • m := by
  let δ : S → M := fun s => s • m - MulOpposite.op s • m
  have hδ : ∀ s s' : S, δ (s * s') = s • δ s' + MulOpposite.op s' • δ s := by
    intro s s'
    show (s * s') • m - MulOpposite.op (s * s') • m
      = s • (s' • m - MulOpposite.op s' • m)
        + MulOpposite.op s' • (s • m - MulOpposite.op s • m)
    rw [smul_sub, smul_sub, MulOpposite.op_mul]
    simp only [mul_smul, smul_comm s (MulOpposite.op s') m]
    abel
  have hδone : δ 1 = 0 := by
    show (1 : S) • m - MulOpposite.op (1 : S) • m = 0
    rw [one_smul, MulOpposite.op_one, one_smul, sub_self]
  have hδadd : ∀ s s' : S, δ (s + s') = δ s + δ s' := by
    intro s s'
    show (s + s') • m - MulOpposite.op (s + s') • m
      = (s • m - MulOpposite.op s • m) + (s' • m - MulOpposite.op s' • m)
    rw [add_smul, MulOpposite.op_add, add_smul]
    abel
  have hδzero : δ 0 = 0 := by
    show (0 : S) • m - MulOpposite.op (0 : S) • m = 0
    rw [zero_smul, MulOpposite.op_zero, zero_smul, sub_self]
  let F : S → TrivSqZeroExt S M := fun s => (s, δ s)
  let h : S →+* TrivSqZeroExt S M :=
  { toFun := F
    map_one' := by
      show F 1 = 1
      rw [show F 1 = ((1 : S), δ 1) from rfl, hδone]
      rfl
    map_mul' := fun s s' => by
      show F (s * s') = F s * F s'
      apply TrivSqZeroExt.ext
      · rw [TrivSqZeroExt.fst_mul]; rfl
      · rw [TrivSqZeroExt.snd_mul]; exact hδ s s'
    map_zero' := by
      show F 0 = 0
      rw [show F 0 = ((0 : S), δ 0) from rfl, hδzero]
      rfl
    map_add' := fun s s' => by
      show F (s + s') = F s + F s'
      apply TrivSqZeroExt.ext
      · rw [TrivSqZeroExt.fst_add]; rfl
      · rw [TrivSqZeroExt.snd_add]; exact hδadd s s' }
  have hgf : (TrivSqZeroExt.inlHom S M).comp f = h.comp f := by
    apply RingHom.ext; intro r
    apply TrivSqZeroExt.ext
    · rw [RingHom.comp_apply, RingHom.comp_apply, TrivSqZeroExt.inlHom_apply,
        TrivSqZeroExt.fst_inl]
      rw [show (h (f r)).fst = f r from rfl]
    · rw [RingHom.comp_apply, RingHom.comp_apply, TrivSqZeroExt.inlHom_apply,
        TrivSqZeroExt.snd_inl]
      rw [show (h (f r)).snd = δ (f r) from rfl]
      have hfr : δ (f r) = 0 := by
        show f r • m - MulOpposite.op (f r) • m = 0
        rw [hm r]; simp
      rw [hfr]
  have key := hf (TrivSqZeroExt.inlHom S M) h hgf
  have h2 : ((TrivSqZeroExt.inlHom S M) d).snd = (h d).snd :=
    congrArg (fun φ : S →+* TrivSqZeroExt S M => (φ d).snd) key
  rw [TrivSqZeroExt.inlHom_apply, TrivSqZeroExt.snd_inl,
    show (h d).snd = δ d from rfl] at h2
  exact eq_of_sub_eq_zero (by simpa [δ] using h2.symm)

/-- Silver's step applied inside the `R`-balanced tensor product `S ⊗[R] S` with `m = 1 ⊗ 1`,
which is fixed by the image of `R`.  This is the hypothesis of the Mazet presentation. -/
theorem tmul_eq_of_isEpic {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : IsEpic f) (d : S) :
    BalancedTensor.tmul f d 1 = BalancedTensor.tmul f 1 d := by
  letI : SMul S (BalancedTensor f) := ⟨fun s m => BalancedTensor.smulLeft f s m⟩
  letI : Module S (BalancedTensor f) := {
    smul := fun s m => BalancedTensor.smulLeft f s m
    one_smul := fun m => by
      show BalancedTensor.smulLeft f 1 m = m
      rw [BalancedTensor.smulLeft_one]; rfl
    mul_smul := fun s t m => by
      show BalancedTensor.smulLeft f (s * t) m
        = BalancedTensor.smulLeft f s (BalancedTensor.smulLeft f t m)
      rw [BalancedTensor.smulLeft_mul]; rfl
    smul_zero := fun s => map_zero _
    smul_add := fun s x y => map_add _ x y
    add_smul := fun s t m => by
      show BalancedTensor.smulLeft f (s + t) m
        = BalancedTensor.smulLeft f s m + BalancedTensor.smulLeft f t m
      rw [BalancedTensor.smulLeft_add]; rfl
    zero_smul := fun m => by
      show BalancedTensor.smulLeft f 0 m = 0
      have h0 : BalancedTensor.smulLeft f 0
          = (0 : BalancedTensor f →+ BalancedTensor f) := by
        have h : BalancedTensor.smulLeft f 0
            = BalancedTensor.smulLeft f 0 + BalancedTensor.smulLeft f 0 := by
          rw [← BalancedTensor.smulLeft_add, add_zero]
        exact (add_left_cancel (show BalancedTensor.smulLeft f 0 + 0
          = BalancedTensor.smulLeft f 0 + BalancedTensor.smulLeft f 0 by
            rw [add_zero]; exact h)).symm
      rw [h0]; rfl }
  letI : SMul Sᵐᵒᵖ (BalancedTensor f) :=
    ⟨fun s m => BalancedTensor.smulRight f (MulOpposite.unop s) m⟩
  letI : Module Sᵐᵒᵖ (BalancedTensor f) := {
    smul := fun s m => BalancedTensor.smulRight f (MulOpposite.unop s) m
    one_smul := fun m => by
      show BalancedTensor.smulRight f (MulOpposite.unop (1 : Sᵐᵒᵖ)) m = m
      rw [MulOpposite.unop_one, BalancedTensor.smulRight_one]; rfl
    mul_smul := fun s t m => by
      show BalancedTensor.smulRight f (MulOpposite.unop (s * t)) m
        = BalancedTensor.smulRight f (MulOpposite.unop s)
            (BalancedTensor.smulRight f (MulOpposite.unop t) m)
      rw [MulOpposite.unop_mul, BalancedTensor.smulRight_mul]; rfl
    smul_zero := fun s => map_zero _
    smul_add := fun s x y => map_add _ x y
    add_smul := fun s t m => by
      show BalancedTensor.smulRight f (MulOpposite.unop (s + t)) m
        = BalancedTensor.smulRight f (MulOpposite.unop s) m
          + BalancedTensor.smulRight f (MulOpposite.unop t) m
      rw [MulOpposite.unop_add, BalancedTensor.smulRight_add]; rfl
    zero_smul := fun m => by
      show BalancedTensor.smulRight f (MulOpposite.unop (0 : Sᵐᵒᵖ)) m = 0
      have h0 : BalancedTensor.smulRight f 0
          = (0 : BalancedTensor f →+ BalancedTensor f) := by
        have h : BalancedTensor.smulRight f 0
            = BalancedTensor.smulRight f 0 + BalancedTensor.smulRight f 0 := by
          rw [← BalancedTensor.smulRight_add, add_zero]
        exact (add_left_cancel (show BalancedTensor.smulRight f 0 + 0
          = BalancedTensor.smulRight f 0 + BalancedTensor.smulRight f 0 by
            rw [add_zero]; exact h)).symm
      rw [MulOpposite.unop_zero, h0]; rfl }
  letI : SMulCommClass S Sᵐᵒᵖ (BalancedTensor f) := {
    smul_comm := fun s s' m =>
      congrArg (fun φ : BalancedTensor f →+ BalancedTensor f => φ m)
        (BalancedTensor.smulLeft_smulRight f s (MulOpposite.unop s')) }
  have hm : ∀ r : R, f r • (BalancedTensor.tmul f 1 1)
      = MulOpposite.op (f r) • (BalancedTensor.tmul f 1 1) := fun r =>
    BalancedTensor.smulLeft_eq_smulRight_tmul_one_one f r
  have h := mul_eq_of_isEpic (M := BalancedTensor f) f hf (BalancedTensor.tmul f 1 1) hm d
  have h1 : BalancedTensor.tmul f d 1 = d • BalancedTensor.tmul f 1 1 := by
    show BalancedTensor.tmul f d 1 = BalancedTensor.smulLeft f d (BalancedTensor.tmul f 1 1)
    rw [BalancedTensor.smulLeft_tmul, mul_one]
  have h2 : MulOpposite.op d • BalancedTensor.tmul f 1 1 = BalancedTensor.tmul f 1 d := by
    show BalancedTensor.smulRight f d (BalancedTensor.tmul f 1 1) = BalancedTensor.tmul f 1 d
    rw [BalancedTensor.smulRight_tmul, one_mul]
  rw [h1, h, h2]

/-- **The von Neumann regular step.**  Suppose `d = X · f(P) · Y` where `X` is a row over `S`,
`P` a square matrix over the von Neumann regular ring `R`, `Y` a column over `S`, and both
`X · f(P)` and `f(P) · Y` are matrices over `f(R)`.  Then `d` is in the range of `f`.

This is the computation in [B. J. Gardner, *Epimorphisms of regular rings*, Comment. Math. Univ.
Carolineae **16** (1975), Theorem 1.6]. -/
theorem exists_preimage_of_matrix_eq {R S : Type u} [Ring R] [Ring S]
    [VonNeumannRegularRing R] (f : R →+* S) {n : ℕ}
    (X : Matrix (Fin 1) (Fin n) S) (P : Matrix (Fin n) (Fin n) R)
    (Y : Matrix (Fin n) (Fin 1) S)
    (hX : ∃ P' : Matrix (Fin 1) (Fin n) R, X * P.map f = P'.map f)
    (hY : ∃ Q' : Matrix (Fin n) (Fin 1) R, P.map f * Y = Q'.map f) :
    ∃ r : R, f r = (X * P.map f * Y) 0 0 := by
  obtain ⟨P', hP'⟩ := hX
  obtain ⟨Q', hQ'⟩ := hY
  obtain ⟨T, hT⟩ :=
    (StarRegular.vonNeumannRegularRing_matrix (U := R) n).exists_mul_inverse P
  have hmap : P.map f * T.map f * P.map f = P.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hT]
  have hmid : P.map f * (T.map f * (P.map f * Y)) = P.map f * Y := by
    rw [← Matrix.mul_assoc (P.map f) (T.map f) (P.map f * Y),
      ← Matrix.mul_assoc (P.map f * T.map f) (P.map f) Y, hmap]
  have keyeq : X * P.map f * Y = P'.map f * T.map f * Q'.map f := by
    rw [← hP', ← hQ']
    calc X * P.map f * Y
        = X * (P.map f * Y) := by rw [Matrix.mul_assoc]
      _ = X * (P.map f * (T.map f * (P.map f * Y))) := by rw [hmid]
      _ = X * P.map f * T.map f * (P.map f * Y) := by simp only [Matrix.mul_assoc]
  refine ⟨(P' * T * Q') 0 0, ?_⟩
  rw [keyeq, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

theorem stenstromVnRegularU {R S : Type u} [Ring R] [Ring S] [VonNeumannRegularRing R]
    (f : R →+* S) (hf : IsEpic f) : Function.Surjective f := by
  intro d
  obtain ⟨n, X, P, Y, hX, hY, hd⟩ := mazetPresentation f (tmul_eq_of_isEpic f hf) d
  obtain ⟨r, hr⟩ := exists_preimage_of_matrix_eq f X P Y hX hY
  exact ⟨r, hr.trans hd.symm⟩


end Work.Section3.EpicSurjectiveUniverse
