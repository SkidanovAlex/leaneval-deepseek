import Submission.E8Weights
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm
import Submission.Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators
import Submission.Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota
import Mathlib.Tactic.NoncommRing

/-!
# The triangular-decomposition spanning of `U(e₈)`

The enveloping algebra `U = U(e₈)` is spanned by the "sorted monomials"
`f₁^{a₁}⋯h₁^{b₁}⋯e₁^{c₁}⋯`, i.e. products of a monomial in the negative generators, a monomial in
the Cartan generators and a monomial in the positive generators, in that order.

The only inputs are the three Serre commutation relations in `U(e₈)`
(`E8Weights.commutator_E_F`, `commutator_H_E`, `commutator_H_F`); no PBW basis is required.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra

noncomputable section
open scoped BigOperators

namespace Submission.E8PBW

open Submission.E8Weights

abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

lemma E8_symm (i j : Fin 8) : E8 i j = E8 j i :=
  Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm.1 i j

/-- A monomial in the negative generators. -/
def fmono (a : List (Fin 8)) : U := (a.map f).prod

/-- A monomial in the Cartan generators. -/
def hmono (b : List (Fin 8)) : U := (b.map h).prod

/-- A monomial in the positive generators. -/
def emono (c : List (Fin 8)) : U := (c.map e).prod

@[simp] lemma fmono_nil : fmono [] = 1 := rfl
@[simp] lemma hmono_nil : hmono [] = 1 := rfl
@[simp] lemma emono_nil : emono [] = 1 := rfl

@[simp] lemma fmono_cons (i : Fin 8) (a : List (Fin 8)) : fmono (i :: a) = f i * fmono a := rfl
@[simp] lemma hmono_cons (i : Fin 8) (b : List (Fin 8)) : hmono (i :: b) = h i * hmono b := rfl
@[simp] lemma emono_cons (i : Fin 8) (c : List (Fin 8)) : emono (i :: c) = e i * emono c := rfl

@[simp] lemma fmono_singleton (i : Fin 8) : fmono [i] = f i := by simp [fmono]
@[simp] lemma hmono_singleton (i : Fin 8) : hmono [i] = h i := by simp [hmono]
@[simp] lemma emono_singleton (i : Fin 8) : emono [i] = e i := by simp [emono]

lemma fmono_append (a a' : List (Fin 8)) : fmono (a ++ a') = fmono a * fmono a' := by
  simp [fmono, List.map_append, List.prod_append]

lemma hmono_append (b b' : List (Fin 8)) : hmono (b ++ b') = hmono b * hmono b' := by
  simp [hmono, List.map_append, List.prod_append]

lemma emono_append (c c' : List (Fin 8)) : emono (c ++ c') = emono c * emono c' := by
  simp [emono, List.map_append, List.prod_append]

/-- The span of the sorted monomials. -/
def S : Submodule ℂ U :=
  Submodule.span ℂ {u : U | ∃ a b c : List (Fin 8), u = fmono a * hmono b * emono c}

/-- The span of `f`-monomials followed by `h`-monomials. -/
def SH : Submodule ℂ U :=
  Submodule.span ℂ {u : U | ∃ a b : List (Fin 8), u = fmono a * hmono b}

/-- The span of `h`-monomials followed by `e`-monomials. -/
def HE : Submodule ℂ U :=
  Submodule.span ℂ {u : U | ∃ b c : List (Fin 8), u = hmono b * emono c}

lemma fmono_mem (a b c : List (Fin 8)) : fmono a * hmono b * emono c ∈ S :=
  Submodule.subset_span ⟨a, b, c, rfl⟩

lemma fmono_hmono_mem_S (a b : List (Fin 8)) : fmono a * hmono b ∈ S := by
  simpa using fmono_mem a b []

lemma fmono_hmono_mem_SH (a b : List (Fin 8)) : fmono a * hmono b ∈ SH :=
  Submodule.subset_span ⟨a, b, rfl⟩

lemma hmono_emono_mem_HE (b c : List (Fin 8)) : hmono b * emono c ∈ HE :=
  Submodule.subset_span ⟨b, c, rfl⟩

lemma SH_le_S : SH ≤ S := by
  refine Submodule.span_le.mpr ?_
  rintro u ⟨a, b, rfl⟩
  exact fmono_hmono_mem_S a b

lemma HE_le_S : HE ≤ S := by
  refine Submodule.span_le.mpr ?_
  rintro u ⟨b, c, rfl⟩
  simpa using fmono_mem [] b c

lemma one_mem_S : (1 : U) ∈ S := by
  simpa using fmono_mem [] [] []

/-! ## The commutation lemmas -/

/-- `hᵢ` pushed to the right of a negative monomial:
`hᵢ f^{a} = f^{a} hᵢ - (∑_{j ∈ a} Aᵢⱼ) f^{a}`. -/
lemma h_mul_fmono (i : Fin 8) (a : List (Fin 8)) :
    h i * fmono a = fmono a * h i
      - ((a.map (fun j => (E8 i j : ℤ))).sum : ℂ) • fmono a := by
  induction a with
  | nil => simp
  | cons j a ih =>
      rw [fmono_cons, ← mul_assoc, h_mul_f_comm, sub_mul, smul_mul_assoc, mul_assoc, ih,
        List.map_cons, List.sum_cons, Int.cast_add]
      noncomm_ring
      module

lemma h_mul_fmono_mem_SH (i : Fin 8) (a : List (Fin 8)) : h i * fmono a ∈ SH := by
  rw [h_mul_fmono]
  refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · simpa using fmono_hmono_mem_SH a [i]
  · simpa using fmono_hmono_mem_SH a []

/-- `hᵢ` commutes with a Cartan monomial. -/
lemma h_mul_hmono (i : Fin 8) (b : List (Fin 8)) : h i * hmono b = hmono (i :: b) := rfl

lemma f_mul_mem_S (i : Fin 8) {u : U} (hu : u ∈ S) : f i * u ∈ S := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, b, c, rfl⟩ := hu
      have hh : f i * (fmono a * hmono b * emono c) = fmono (i :: a) * hmono b * emono c := by
        rw [fmono_cons]; noncomm_ring
      rw [hh]; exact fmono_mem (i :: a) b c
  | zero => simp
  | add x y _ _ ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ihx

lemma f_mul_mem_SH (i : Fin 8) {u : U} (hu : u ∈ SH) : f i * u ∈ SH := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, b, rfl⟩ := hu
      have hh : f i * (fmono a * hmono b) = fmono (i :: a) * hmono b := by
        rw [fmono_cons]; noncomm_ring
      rw [hh]; exact fmono_hmono_mem_SH (i :: a) b
  | zero => simp
  | add x y _ _ ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ihx

/-- `eᵢ` pushed to the right of a Cartan monomial: `eᵢ h^{b} ∈ span{h^{b'} eᵢ}`. -/
lemma e_mul_hmono (i : Fin 8) (b : List (Fin 8)) : e i * hmono b ∈ HE := by
  induction b with
  | nil => simpa using hmono_emono_mem_HE [] [i]
  | cons j b ih =>
      have hcomm : e i * h j = h j * e i - (E8 i j : ℂ) • e i := by
        have hh : h j * e i - e i * h j = (E8 j i : ℂ) • e i := commutator_H_E j i
        rw [E8_symm] at hh
        rw [sub_eq_iff_eq_add] at hh
        rw [add_comm] at hh
        rw [hh]; noncomm_ring
      have hsplit : e i * hmono (j :: b) = h j * (e i * hmono b)
          - (E8 i j : ℂ) • (e i * hmono b) := by
        rw [hmono_cons, ← mul_assoc, hcomm, sub_mul, smul_mul_assoc, mul_assoc]
      rw [hsplit]
      refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ih)
      refine Submodule.span_induction (p := fun v _ => h j * v ∈ HE) ?_ ?_ ?_ ?_ ih
      · rintro v ⟨b', c', rfl⟩
        have hz : h j * (hmono b' * emono c') = hmono (j :: b') * emono c' := by
          rw [hmono_cons]; noncomm_ring
        rw [hz]; exact hmono_emono_mem_HE (j :: b') c'
      · simp
      · intro x y _ _ ihx ihy; rw [mul_add]; exact Submodule.add_mem _ ihx ihy
      · intro d x _ ihx; rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ihx

lemma e_mul_mem_HE (i : Fin 8) {u : U} (hu : u ∈ HE) : e i * u ∈ HE := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨b, c, rfl⟩ := hu
      have hh : e i * (hmono b * emono c) = (e i * hmono b) * emono c := by noncomm_ring
      rw [hh]
      have h2 : (e i * hmono b) * emono c ∈ HE := by
        refine Submodule.span_induction (p := fun v _ => v * emono c ∈ HE) ?_ ?_ ?_ ?_
          (e_mul_hmono i b)
        · rintro v ⟨b', c', rfl⟩
          have hz : (hmono b' * emono c') * emono c = hmono b' * emono (c' ++ c) := by
            rw [emono_append]; noncomm_ring
          rw [hz]; exact hmono_emono_mem_HE b' (c' ++ c)
        · simp
        · intro x y _ _ ihx ihy; rw [add_mul]; exact Submodule.add_mem _ ihx ihy
        · intro d x _ ihx; rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ihx
      exact h2
  | zero => simp
  | add x y _ _ ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
  | smul d x _ ihx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ihx

lemma emono_mul_hmono (c b : List (Fin 8)) : emono c * hmono b ∈ HE := by
  induction c with
  | nil => simpa using hmono_emono_mem_HE b []
  | cons i c ih =>
      rw [emono_cons, mul_assoc]
      exact e_mul_mem_HE i ih

/-- `eᵢ` pushed to the right of a negative monomial. -/
lemma e_mul_fmono (i : Fin 8) (a : List (Fin 8)) : e i * fmono a ∈ S := by
  induction a with
  | nil => simpa using fmono_mem [] [] [i]
  | cons j a ih =>
      have hcomm : e i * f j = f j * e i + (if i = j then h i else 0) := by
        have h1 : e i * f j = (if i = j then h i else 0) + f j * e i :=
          sub_eq_iff_eq_add.mp (commutator_E_F i j)
        rw [h1, add_comm]
      have hsplit : e i * fmono (j :: a) = f j * (e i * fmono a)
          + (if i = j then h i * fmono a else 0) := by
        rw [fmono_cons, ← mul_assoc, hcomm, add_mul, mul_assoc, ite_mul, zero_mul]
      rw [hsplit]
      refine Submodule.add_mem _ (f_mul_mem_S j ih) ?_
      by_cases hij : i = j
      · rw [if_pos hij]; exact SH_le_S (h_mul_fmono_mem_SH i a)
      · rw [if_neg hij]; exact Submodule.zero_mem _

/-- `S` is closed under right multiplication by an element of `HE`. -/
lemma mul_mem_S_of_mem_HE {u : U} (hu : u ∈ S) {w : U} (hw : w ∈ HE) : u * w ∈ S := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, b, c, rfl⟩ := hu
      induction hw using Submodule.span_induction with
      | mem w hw =>
          obtain ⟨b', c', rfl⟩ := hw
          have heq : fmono a * hmono b * emono c * (hmono b' * emono c')
              = (fmono a * hmono b * (emono c * hmono b')) * emono c' := by noncomm_ring
          rw [heq]
          refine Submodule.span_induction (p := fun v _ =>
            (fmono a * hmono b * v) * emono c' ∈ S) ?_ ?_ ?_ ?_ (emono_mul_hmono c b')
          · rintro v ⟨b'', c'', rfl⟩
            have hz : (fmono a * hmono b * (hmono b'' * emono c'')) * emono c'
                = fmono a * hmono (b ++ b'') * emono (c'' ++ c') := by
              rw [hmono_append, emono_append]; noncomm_ring
            rw [hz]; exact fmono_mem a (b ++ b'') (c'' ++ c')
          · simp
          · intro x y _ _ ihx ihy; rw [mul_add, add_mul]; exact Submodule.add_mem _ ihx ihy
          · intro d x _ ihx
            rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ ihx
      | zero => simp
      | add x y _ _ ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
      | smul d x _ ihx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ihx
  | zero => simp
  | add x y _ _ ihx ihy => rw [add_mul]; exact Submodule.add_mem _ ihx ihy
  | smul d x _ ihx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ihx

lemma h_mul_mem_S (i : Fin 8) {u : U} (hu : u ∈ S) : h i * u ∈ S := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, b, c, rfl⟩ := hu
      have heq : h i * (fmono a * hmono b * emono c)
          = (h i * fmono a) * (hmono b * emono c) := by noncomm_ring
      rw [heq]
      exact mul_mem_S_of_mem_HE (SH_le_S (h_mul_fmono_mem_SH i a)) (hmono_emono_mem_HE b c)
  | zero => simp
  | add x y _ _ ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x _ ihx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ihx

lemma e_mul_mem_S (i : Fin 8) {u : U} (hu : u ∈ S) : e i * u ∈ S := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, b, c, rfl⟩ := hu
      have hh : e i * (fmono a * hmono b * emono c)
          = (e i * fmono a) * (hmono b * emono c) := by noncomm_ring
      rw [hh]
      exact mul_mem_S_of_mem_HE (e_mul_fmono i a) (hmono_emono_mem_HE b c)
  | zero => simp
  | add x y _ _ ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
  | smul d x _ ihx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ihx

/-! ## `S` is everything -/

/-- The algebra of elements which multiply `S` into itself on the right. -/
def T : Subalgebra ℂ U where
  carrier := {u : U | ∀ v ∈ S, u * v ∈ S}
  one_mem' := by intro v hv; simpa using hv
  mul_mem' := by intro a b ha hb v hv; rw [mul_assoc]; exact ha _ (hb v hv)
  add_mem' := by
    intro a b ha hb v hv
    rw [add_mul]; exact Submodule.add_mem _ (ha v hv) (hb v hv)
  zero_mem' := by intro v hv; rw [zero_mul]; exact Submodule.zero_mem _
  algebraMap_mem' := by
    intro c v hv
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ _ hv

lemma iota_mem_T (x : L) : UniversalEnvelopingAlgebra.ι ℂ x ∈ T := by
  let N : LieSubalgebra ℂ L :=
    { carrier := {x : L | UniversalEnvelopingAlgebra.ι ℂ x ∈ T}
      add_mem' := by
        intro x y hx hy
        change UniversalEnvelopingAlgebra.ι ℂ (x + y) ∈ T
        rw [map_add]; exact T.add_mem hx hy
      zero_mem' := by
        change UniversalEnvelopingAlgebra.ι ℂ (0 : L) ∈ T
        rw [map_zero]; exact T.zero_mem
      smul_mem' := by
        intro c x hx
        change UniversalEnvelopingAlgebra.ι ℂ (c • x) ∈ T
        rw [map_smul]; exact T.smul_mem hx c
      lie_mem' := by
        intro x y hx hy
        change UniversalEnvelopingAlgebra.ι ℂ ⁅x, y⁆ ∈ T
        rw [LieHom.map_lie, Ring.lie_def]
        exact T.sub_mem (T.mul_mem hx hy) (T.mul_mem hy hx) }
  have htop : N = ⊤ :=
    Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators CartanMatrix.E₈ N (by
      intro g
      cases g with
      | H i =>
          exact show UniversalEnvelopingAlgebra.ι ℂ (SerreH i) ∈ T from
            fun v hv => h_mul_mem_S i hv
      | E i =>
          exact show UniversalEnvelopingAlgebra.ι ℂ (SerreE i) ∈ T from
            fun v hv => e_mul_mem_S i hv
      | F i =>
          exact show UniversalEnvelopingAlgebra.ι ℂ (SerreF i) ∈ T from
            fun v hv => f_mul_mem_S i hv)
  have : x ∈ N := htop ▸ Submodule.mem_top
  exact this

/-- **`U(e₈)` is spanned by the sorted monomials.** -/
theorem S_eq_top : S = ⊤ := by
  have hT : Algebra.adjoin ℂ (Set.range (fun x : L => UniversalEnvelopingAlgebra.ι ℂ x)) ≤ T :=
    Algebra.adjoin_le_iff.mpr (by rintro _ ⟨x, rfl⟩; exact iota_mem_T x)
  refine le_antisymm le_top ?_
  intro u _
  have hu : u ∈ Algebra.adjoin ℂ (Set.range (fun x : L => UniversalEnvelopingAlgebra.ι ℂ x)) := by
    rw [Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota]; trivial
  have h1 := hT hu
  simpa using h1 (1 : U) one_mem_S

/-! ## The action on a primitive vector -/

section Action

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module U M] [IsScalarTower ℂ U M]
  [SMulCommClass U ℂ M]

/-- A product of raising operators kills a primitive vector. -/
lemma emono_smul_eq (x : M) (he : ∀ i : Fin 8, e i • x = 0) (c : List (Fin 8)) :
    emono c • x = if c = [] then x else 0 := by
  induction c with
  | nil => simp
  | cons i c ih =>
      rw [emono_cons, mul_smul, ih, if_neg (List.cons_ne_nil i c)]
      by_cases hc : c = []
      · subst hc; simpa using he i
      · simp [hc]

/-- A product of Cartan generators acts on a weight vector by a scalar. -/
lemma hmono_smul_eq (x : M) (mu : Fin 8 → ℂ) (hh : ∀ i : Fin 8, h i • x = mu i • x)
    (b : List (Fin 8)) : hmono b • x = (b.map mu).prod • x := by
  induction b with
  | nil => simp
  | cons i b ih =>
      rw [hmono_cons, mul_smul, ih, ← smul_comm ((b.map mu).prod) (h i) x, hh i, smul_smul,
        List.map_cons, List.prod_cons, mul_comm]

/-- The span of the negative monomials applied to a vector. -/
def fspan {M : Type*} [AddCommGroup M] [Module ℂ M] [Module U M] (x : M) : Submodule ℂ M :=
  Submodule.span ℂ (Set.range (fun a : List (Fin 8) => fmono a • x))

/-- **The `f`-span of a primitive vector is stable under `U(e₈)`.** -/
theorem smul_mem_fspan (x : M) (he : ∀ i : Fin 8, e i • x = 0) (mu : Fin 8 → ℂ)
    (hh : ∀ i : Fin 8, h i • x = mu i • x) (u : U) : u • x ∈ fspan x := by
  have hle : ∀ u ∈ S, u • x ∈ fspan x := by
    intro u hu
    refine Submodule.span_induction (p := fun w _ => w • x ∈ fspan x) ?_ ?_ ?_ ?_ hu
    · rintro w ⟨a, b, c, rfl⟩
      rw [mul_smul, mul_smul]
      by_cases hc : c = []
      · subst hc
        rw [emono_nil, one_smul, hmono_smul_eq x mu hh b]
        rw [smul_comm]
        exact Submodule.smul_mem (fspan x) ((b.map mu).prod)
          (Submodule.subset_span ⟨a, rfl⟩)
      · rw [emono_smul_eq x he c, if_neg hc]
        simp
    · simp
    · intro y z _ _ ihy ihz
      rw [add_smul]
      exact Submodule.add_mem _ ihy ihz
    · intro d y _ ihy
      rw [smul_assoc]
      exact Submodule.smul_mem _ _ ihy
  exact hle u (by rw [S_eq_top]; trivial)

end Action

end Submission.E8PBW
