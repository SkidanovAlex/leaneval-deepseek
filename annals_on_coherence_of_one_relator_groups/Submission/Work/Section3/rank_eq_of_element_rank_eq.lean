import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.StarRegular.fgRightIdeal_idempotent
import Submission.Work.ORHughesFree.RankAPI.diagonal_rank
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.ORHughesFree.NaturalExtension.rdim_prod_add
import Submission.Work.ORHughesFree.NaturalExtension.rdim_map_of_leftInverse
import Submission.Work.ORHughesFree.NaturalExtension.dimOf_append_le
import Submission.Work.ORHughesFree.Section3.vnIsoInvariance

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Section3

open Matrix Work.ORHughesFree

open Work.ORHughesFree.NaturalExtension

/-!
# A Sylvester rank function on a von Neumann regular ring is determined by its `1 × 1` values

The main theorem of this file is `rank_eq_of_element_rank_eq`: two Sylvester matrix rank
functions on a von Neumann regular ring `U` which agree on all `1 × 1` matrices agree on *all*
matrices.

The proof is an induction on the number of rows of the matrix.  Let
`A : Matrix (Fin (k+1)) (Fin n) U`, split off its first `k` rows and its last row `w`, so that
the row span of `A` is `M ⊔ span {w}` where `M` is the row span of the first `k` rows (the
lemma `span_range_finAppend` computes the span of a concatenation of two row families).  If `E`
is the idempotent endomorphism of `Uⁿ` with range `M`, then `(1 - E) w = w - E w` with
`E w ∈ M`, so

  `M ⊔ span {w} = M ⊔ span {(1 - E) w}`,

and this is a *direct* sum (the two submodules meet in `0`).

* The key lemma `rdim_sup_eq_add` shows that the row-wise dimension `rdim` is additive on this
  direct sum; the proof uses the linear map `η z = (E z, (1 - E) z)` (whose left inverse is the
  "sum" map `ξ (a, b) = a + b` and which maps the sum onto the product `M × span {(1 - E) w}`)
  together with `rdim_prod_add`.
* `rdim ρ M = ρ.rk B` for the matrix `B` of the first `k` rows, and the dimension of the cyclic
  piece `span {(1 - E) w}` equals `ρ.rk 1 1 (oneByOne g)` for an idempotent `g ∈ U` that only
  depends on the single row `(1 - E) w` (the single-row reduction `rk_row_eq_rk_oneByOne`).
-/

section RingOnly

variable {U : Type*} [Ring U]

/-- For a family of length `1`, the range is the singleton of its value. -/
theorem range_fin_one {n : ℕ} (v : Fin n → U) :
    Set.range (fun _ : Fin 1 => v) = ({v} : Set (Fin n → U)) :=
  Set.range_const

/-- The span of the rows of `A` is the sum of the span of the rows of its first `k` rows and the
span of its last row. -/
theorem span_rows_succ {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) U)
    (v : Fin k → (Fin n → U)) (w : Fin n → U) (hv : ∀ i j, v i j = A i.castSucc j)
    (hw : ∀ j, w j = A (Fin.last k) j) :
    Submodule.span U (Set.range (fun i : Fin (k + 1) => fun j : Fin n => A i j))
      = Submodule.span U (Set.range v) ⊔ Submodule.span U ({w} : Set (Fin n → U)) := by
  have hv' : v = (fun i : Fin k => fun j : Fin n => A i.castSucc j) :=
    funext fun i => funext fun j => hv i j
  have hw' : w = (fun j : Fin n => A (Fin.last k) j) := funext fun j => hw j
  subst hv'
  subst hw'
  have hfam : (fun i : Fin (k + 1) => fun j : Fin n => A i j)
      = Fin.append (fun i : Fin k => fun j : Fin n => A i.castSucc j)
          (fun _ : Fin 1 => fun j : Fin n => A (Fin.last k) j) := by
    funext i j
    induction i using Fin.addCases with
    | left i' =>
      rw [Fin.append_left]
      exact congrArg (fun k => A k j) (Fin.ext (by simp))
    | right i' =>
      rw [Fin.append_right]
      exact congrArg (fun k => A k j) (Fin.ext (by simp))
  rw [hfam, NaturalExtension.span_range_finAppend]
  have hconst : Set.range (fun _ : Fin 1 => (fun j : Fin n => A (Fin.last k) j))
      = ({fun j : Fin n => A (Fin.last k) j} : Set (Fin n → U)) := Set.range_const
  try rw [hconst]

end RingOnly

section Regular

variable {U : Type*} [Ring U] [VonNeumannRegularRing U]

/-- **The outer idempotent of a row.**  For a single row `w` (a `1 × n` matrix) there is an
idempotent `g ∈ U`, generating the right ideal spanned by the entries of `w`, such that
`g * w = w` entrywise and `g` is a right linear combination of the entries. -/
theorem exists_idem_row {n : ℕ} (w : Matrix (Fin 1) (Fin n) U) :
    ∃ g : U, g * g = g ∧ (∀ i : Fin n, g * w 0 i = w 0 i) ∧
      (∃ c : Fin n → U, g = ∑ i, w 0 i * c i) := by
  obtain ⟨g, hg, hspan⟩ :=
    Work.ORHughesFree.StarRegular.exists_idempotent_span_range n (fun i => w 0 i)
  refine ⟨g, hg, ?_, ?_⟩
  · intro i
    have hmem : w 0 i ∈ Submodule.span Uᵐᵒᵖ (Set.range (fun j => w 0 j)) :=
      Submodule.subset_span (Set.mem_range_self i)
    rw [hspan] at hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    rw [MulOpposite.smul_eq_mul_unop] at ha
    calc g * w 0 i = g * (g * MulOpposite.unop a) := by rw [ha]
      _ = (g * g) * MulOpposite.unop a := by rw [mul_assoc]
      _ = g * MulOpposite.unop a := by rw [hg]
      _ = w 0 i := ha
  · have hmem : g ∈ Submodule.span Uᵐᵒᵖ (Set.range (fun j => w 0 j)) := by
      rw [hspan]
      exact Submodule.subset_span (Set.mem_singleton g)
    exact (Work.ORHughesFree.StarRegular.mem_span_range_iff_exists_mul (fun j => w 0 j) g).mp hmem

/-- **Reduction of a single row to a `1 × 1` matrix.**  The rank of a `1 × n` matrix `w` equals
the rank of the `1 × 1` matrix of the idempotent `g` generated by its entries. -/
theorem rk_row_eq_rk_oneByOne (ρ : SylvesterRank U) {n : ℕ} (w : Matrix (Fin 1) (Fin n) U)
    (g : U) (hg : g * g = g) (h1 : ∀ i : Fin n, g * w 0 i = w 0 i)
    (h2 : ∃ c : Fin n → U, g = ∑ i, w 0 i * c i) :
    ρ.rk 1 n w = ρ.rk 1 1 (oneByOne g) := by
  obtain ⟨c, hc⟩ := h2
  have hgw : oneByOne g * w = w := by
    ext i j
    fin_cases i
    simp [Matrix.mul_apply, oneByOne, h1 j]
  have hwD : w * Matrix.of (fun i (_ : Fin 1) => c i) = oneByOne g := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, oneByOne, hc]
  have hle1 : ρ.rk 1 n w ≤ ρ.rk 1 1 (oneByOne g) := by
    rw [← hgw]
    exact ρ.rk_mul_le_left (oneByOne g) w
  have hle2 : ρ.rk 1 1 (oneByOne g) ≤ ρ.rk 1 n w := by
    rw [← hwD]
    exact ρ.rk_mul_le_left w (Matrix.of (fun i (_ : Fin 1) => c i))
  exact le_antisymm hle1 hle2

/-- The row-wise dimension of the span of a single vector is the `1 × 1` rank of the idempotent
generated by its entries. -/
theorem rdim_span_eq_rk_oneByOne (ρ : SylvesterRank U) {n : ℕ} (u : Fin n → U) (g : U)
    (hg : g * g = g) (h1 : ∀ i : Fin n, g * u i = u i)
    (h2 : ∃ c : Fin n → U, g = ∑ i, u i * c i) :
    rdim ρ (Submodule.span U ({u} : Set (Fin n → U))) = ρ.rk 1 1 (oneByOne g) := by
  have h4a : rdim ρ (Submodule.span U ({u} : Set (Fin n → U)))
      = ρ.rk 1 n (fun (_ : Fin 1) (j : Fin n) => u j) := by
    simpa only [range_fin_one] using
      NaturalExtension.rdim_eq_rk_rows ρ (fun (_ : Fin 1) (j : Fin n) => u j)
  rw [h4a, rk_row_eq_rk_oneByOne ρ (fun (_ : Fin 1) (j : Fin n) => u j) g hg h1 h2]

/-- **Additivity of the row-wise dimension.**  Let `M` be the range of an idempotent
endomorphism `E` of `Uⁿ` and let `w ∈ Uⁿ`.  Then the row-wise dimension of `M ⊔ span {w}` splits
as the sum of the dimensions of `M` and of the cyclic submodule `span {(1 - E) w}`.

Indeed `E` fixes `M` and kills `(1 - E) w`, so `M` and `span {(1 - E) w}` meet in `0` and their
sum is `M ⊔ span {w}`.  The linear map `η z = (E z, (1 - E) z)` with values in `Uⁿ × Uⁿ`
satisfies `ξ ∘ η = id` for the "sum" map `ξ (a, b) = a + b` and maps `M ⊔ span {(1-E) w}` onto
the product `M × span {(1-E) w}`, so `rdim` of the sum is `rdim` of that product, which is the sum
of the two dimensions by `rdim_prod_add`. -/
theorem rdim_sup_eq_add (ρ : SylvesterRank U) {n : ℕ} (M : Submodule U (Fin n → U))
    (E : Module.End U (Fin n → U)) (hE : E * E = E) (hM : LinearMap.range E = M) (w : Fin n → U) :
    rdim ρ (M ⊔ Submodule.span U ({w} : Set (Fin n → U)))
      = rdim ρ M + rdim ρ (Submodule.span U ({(1 - E) w} : Set (Fin n → U))) := by
  set C : Submodule U (Fin n → U) := Submodule.span U ({(1 - E) w} : Set (Fin n → U)) with hCdef
  have hEM : ∀ x ∈ M, E x = x := by
    intro x hx
    rw [← hM] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy, ← Module.End.mul_apply, hE]
  have hE1 : E ((1 - E) w) = 0 := by
    have h : E ((1 - E) w) = (E * (1 - E)) w := by rw [Module.End.mul_apply]
    rw [h, show E * (1 - E) = 0 from by rw [mul_sub, mul_one, hE, sub_self],
      LinearMap.zero_apply]
  have hEC : ∀ y ∈ C, E y = 0 := by
    intro y hy
    rw [hCdef] at hy
    refine Submodule.span_induction (p := fun y _ => E y = 0) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz, hE1]
    · exact map_zero E
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, add_zero]
    · intro c a _ ha
      rw [map_smul, ha, smul_zero]
  have h1EM : ∀ x ∈ M, (1 - E) x = 0 := by
    intro x hx
    rw [LinearMap.sub_apply, Module.End.one_apply, hEM x hx, sub_self]
  have h1EC : ∀ y ∈ C, (1 - E) y = y := by
    intro y hy
    rw [LinearMap.sub_apply, Module.End.one_apply, hEC y hy, sub_zero]
  have hw : w = E w + (1 - E) w := by
    conv_rhs =>
      rw [← LinearMap.add_apply,
        show E + (1 - E) = 1 from by rw [add_comm, sub_add_cancel], Module.End.one_apply]
  have hEwM : E w ∈ M := by
    rw [← hM]
    exact LinearMap.mem_range_self E w
  have h1Ew : (1 - E) w = w - E w := by
    rw [LinearMap.sub_apply, Module.End.one_apply]
  have hsup : M ⊔ C = M ⊔ Submodule.span U ({w} : Set (Fin n → U)) := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · rw [hCdef, Submodule.span_le, Set.singleton_subset_iff, h1Ew]
      exact Submodule.sub_mem _
        (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton w)))
        (Submodule.mem_sup_left hEwM)
    · rw [Submodule.span_le, Set.singleton_subset_iff, hw]
      refine Submodule.add_mem_sup hEwM ?_
      rw [hCdef]
      exact Submodule.subset_span (Set.mem_singleton ((1 - E) w))
  -- the linear maps `η` and `ξ`
  set eprod : ((Fin n → U) × (Fin n → U)) ≃ₗ[U] (Fin (n + n) → U) :=
    Work.ORHughesFree.Section3.prodFinLinearEquiv n n with heprod
  set η : (Fin n → U) →ₗ[U] (Fin (n + n) → U) :=
    eprod.toLinearMap ∘ₗ (E.prod ((1 : Module.End U (Fin n → U)) - E)) with hηdef
  set ξ : (Fin (n + n) → U) →ₗ[U] (Fin n → U) :=
    (LinearMap.fst U (Fin n → U) (Fin n → U) + LinearMap.snd U (Fin n → U) (Fin n → U)) ∘ₗ
      eprod.symm.toLinearMap with hξdef
  have hξη : ξ ∘ₗ η = LinearMap.id := by
    apply LinearMap.ext
    intro z
    simp only [hηdef, hξdef, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prod_apply, Function.prod_apply]
    rw [← LinearMap.add_apply,
      show E + (1 - E) = 1 from by rw [add_comm, sub_add_cancel], Module.End.one_apply]
    rfl
  have hEA : ∀ a ∈ M, ∀ b ∈ C, E (a + b) = a := by
    intro a ha b hb
    rw [map_add E a b, hEM a ha, hEC b hb, add_zero]
  have h1EA : ∀ a ∈ M, ∀ b ∈ C, (1 - E) (a + b) = b := by
    intro a ha b hb
    rw [LinearMap.sub_apply, Module.End.one_apply, hEA a ha b hb]
    abel
  have hmap : Submodule.map η (M ⊔ C) = Submodule.map eprod.toLinearMap (Submodule.prod M C) := by
    refine le_antisymm ?_ ?_
    · intro z hz
      rw [Submodule.mem_map] at hz ⊢
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
      refine ⟨(a, b), Submodule.mem_prod.mpr ⟨ha, hb⟩, ?_⟩
      rw [← hab, hηdef, LinearMap.comp_apply, LinearMap.prod_apply, Function.prod_apply,
        hEA a ha b hb, h1EA a ha b hb]
    · intro z hz
      rw [Submodule.mem_map] at hz ⊢
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
      rw [Submodule.mem_prod] at hab
      refine ⟨a + b, Submodule.mem_sup.mpr ⟨a, hab.1, b, hab.2, rfl⟩, ?_⟩
      rw [hηdef, LinearMap.comp_apply, LinearMap.prod_apply, Function.prod_apply,
        hEA a hab.1 b hab.2, h1EA a hab.1 b hab.2]
  have hstep : rdim ρ (M ⊔ C) = rdim ρ (Submodule.map η (M ⊔ C)) :=
    (NaturalExtension.rdim_map_of_leftInverse ρ hξη (M ⊔ C)).symm
  rw [← hsup, hstep, hmap]
  exact NaturalExtension.rdim_prod_add ρ eprod M C

end Regular

section Main

variable {U : Type*} [Ring U] [VonNeumannRegularRing U]

/-- **The main induction.**  Two Sylvester rank functions on a von Neumann regular ring which
agree on the `1 × 1` matrices agree on every matrix. -/
theorem rk_eq_of_element_rank_eq_aux (ρ₁ ρ₂ : SylvesterRank U)
    (h : ∀ x : U, ρ₁.rk 1 1 (oneByOne x) = ρ₂.rk 1 1 (oneByOne x)) :
    ∀ (k n : ℕ) (A : Matrix (Fin k) (Fin n) U), ρ₁.rk k n A = ρ₂.rk k n A := by
  intro k
  induction k with
  | zero =>
    intro n A
    have h0 : A = 0 := Subsingleton.elim A 0
    rw [h0, ρ₁.rk_zero, ρ₂.rk_zero]
  | succ k ih =>
    intro n A
    set B : Matrix (Fin k) (Fin n) U := A.submatrix Fin.castSucc id with hBdef
    set v : Fin k → (Fin n → U) := fun i => fun j => A i.castSucc j with hvdef
    set w : Fin n → U := fun j => A (Fin.last k) j with hwdef
    obtain ⟨E, hE, hErange⟩ := Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux v
    set M : Submodule U (Fin n → U) := Submodule.span U (Set.range v) with hMdef
    have hME : LinearMap.range E = M := by rw [hErange, hMdef]
    have hspan : Submodule.span U (Set.range (fun i : Fin (k + 1) => fun j : Fin n => A i j))
        = M ⊔ Submodule.span U ({w} : Set (Fin n → U)) := by
      rw [span_rows_succ A v w (fun i j => rfl) (fun j => rfl), ← hMdef]
    obtain ⟨g, hg, hg1, hg2⟩ :=
      exists_idem_row (fun (_ : Fin 1) (j : Fin n) =>
        ((1 : Module.End U (Fin n → U)) - E) w j)
    have hg1' : ∀ i : Fin n, g * ((1 - E) w) i = ((1 - E) w) i := hg1
    have hg2' : ∃ c : Fin n → U, g = ∑ i, ((1 - E) w) i * c i := hg2
    have hkey : ∀ ρ : SylvesterRank U,
        ρ.rk (k + 1) n A = ρ.rk k n B + ρ.rk 1 1 (oneByOne g) := by
      intro ρ
      have hA : ρ.rk (k + 1) n A = rdim ρ (M ⊔ Submodule.span U ({w} : Set (Fin n → U))) := by
        rw [← NaturalExtension.rdim_eq_rk_rows ρ A, hspan]
      have hadd := rdim_sup_eq_add ρ M E hE hME w
      have hM' : rdim ρ M = ρ.rk k n B := by
        have hMeq : M = Submodule.span U (Set.range (fun i : Fin k => fun j : Fin n => B i j)) := by
          rw [hMdef]
          rfl
        rw [hMeq, NaturalExtension.rdim_eq_rk_rows ρ B]
      have hC' : rdim ρ (Submodule.span U ({(1 - E) w} : Set (Fin n → U)))
          = ρ.rk 1 1 (oneByOne g) :=
        rdim_span_eq_rk_oneByOne ρ ((1 - E) w) g hg hg1' hg2'
      rw [hA, hadd, hM', hC']
    calc ρ₁.rk (k + 1) n A = ρ₁.rk k n B + ρ₁.rk 1 1 (oneByOne g) := hkey ρ₁
      _ = ρ₂.rk k n B + ρ₂.rk 1 1 (oneByOne g) := by rw [ih n B, h g]
      _ = ρ₂.rk (k + 1) n A := (hkey ρ₂).symm

end Main

theorem rank_eq_of_element_rank_eq {U : Type*} [Ring U]
    [Work.ORHughesFree.VonNeumannRegularRing U]
    (ρ₁ ρ₂ : Work.ORHughesFree.SylvesterRank U)
    (h : ∀ x : U,
      ρ₁.rk 1 1 (Work.ORHughesFree.oneByOne x) = ρ₂.rk 1 1 (Work.ORHughesFree.oneByOne x)) :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U), ρ₁.rk n m A = ρ₂.rk n m A :=
  fun n m A => rk_eq_of_element_rank_eq_aux ρ₁ ρ₂ h n m A

end Work.Section3
