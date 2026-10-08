import Mathlib
import Submission.Work.Models.Basic
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.bruhat
import Submission.Work.Models.PSL2.w_facts
import Submission.Work.Models.PSL2.U_facts
import Submission.Work.Models.PSL2.card_D

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.B_stronglyEmbedded`

The standard Borel `B` of `SL(2,F)` (`F` a finite field of characteristic `2`), i.e. the
subgroup of upper triangular matrices, is **strongly embedded** in `SL(2,F)`:

`B ≠ ⊤`, `|B|` is even, and for every `g ∉ B` the two-point stabiliser `B ⊓ B^g` has odd
order.

The three ingredients are:

* `B ≠ ⊤`: the Weyl element `w = !![0,1;1,0]` is not upper triangular (`w_facts`).
* `Even |B|`: `B` contains the unipotent radical `U` of order `|F|`, which is even.
* `Odd |B ⊓ B^g|` for `g ∉ B`: the Bruhat decomposition writes `g = b₁ w b₂` with
  `b₁, b₂ ∈ B`; conjugating, `B ⊓ B^g = (B ⊓ B^w)^{b₁}`, and `B ⊓ B^w = D`
  (`inf_conj_w`) is the diagonal torus, whose order `|F| - 1` is odd because `|F|` is a
  power of `2`.
-/

namespace Work.Models.PSL2

open Matrix

variable {F : Type*} [Field F] [CharP F 2]

/-! ## Conjugation by the Weyl element -/

/-- Conjugation by the Weyl element `w = !![0,1;1,0]` transposes a `2 × 2` matrix across the
*anti*diagonal: it swaps the two diagonal entries and it swaps the two off-diagonal
entries. -/
lemma w_conj_coe (A : SL2 F) :
    ((w (F := F) * A * w (F := F) : SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = !![(A : Matrix (Fin 2) (Fin 2) F) 1 1, (A : Matrix (Fin 2) (Fin 2) F) 1 0;
           (A : Matrix (Fin 2) (Fin 2) F) 0 1, (A : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, w_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Fin.isValue, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, one_mul,
        mul_zero, mul_one, zero_add, add_zero]

/-- **The Borel meets its `w`-conjugate in the split torus**: `B ⊓ B^w = D`.

An upper triangular matrix `A = !![a,b;0,d]` whose `w`-conjugate `w A w⁻¹ = !![d,0;b,a]` is
again upper triangular must have `b = 0`, i.e. be diagonal.  Conversely a diagonal matrix is
upper triangular and `w`-conjugation inverts it (`w_facts`), so it stays diagonal. -/
theorem inf_conj_w {F : Type*} [Field F] [CharP F 2] :
    Work.Models.PSL2.B (F := F) ⊓
        (Work.Models.PSL2.B (F := F)).map
          (MulAut.conj (Work.Models.PSL2.w (F := F))).toMonoidHom
      = Work.Models.PSL2.D (F := F) := by
  have hwinv : (w (F := F))⁻¹ = w (F := F) :=
    inv_eq_of_mul_eq_one_right (w_invol (F := F))
  apply le_antisymm
  · intro A hA
    obtain ⟨hAB, hAc⟩ := Subgroup.mem_inf.mp hA
    rw [mem_D_iff']
    refine ⟨?_, hAB⟩
    -- `A` is also in `B^w`, i.e. `w⁻¹ A w ∈ B`, and that matrix has `(1,0)`-entry `A 0 1`
    have hAw : w (F := F) * A * w (F := F) ∈ B (F := F) := by
      have h := (mem_conj_iff (H := B (F := F)) (g := w (F := F)) (x := A)).mp hAc
      rwa [hwinv] at h
    have hb : ((w (F := F) * A * w (F := F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hAw
    rw [w_conj_coe] at hb
    simpa using hb
  · intro A hA
    rw [mem_D_iff'] at hA
    obtain ⟨h01, h10⟩ := hA
    refine Subgroup.mem_inf.mpr ⟨h10, ?_⟩
    refine (mem_conj_iff (H := B (F := F)) (g := w (F := F)) (x := A)).mpr ?_
    have hmat : ((w (F := F) * A * w (F := F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [w_conj_coe]
      simpa using h01
    rw [hwinv]
    exact hmat

/-! ## The parity of the two subgroups -/

/-- The split torus `D ≅ Fˣ` of `SL(2,F)` has **odd** order for `F` a finite field of
characteristic `2`: `|D| = |F| - 1` and `|F| = 2^n`, so `|D| = 2^n - 1` is odd. -/
theorem odd_card_D {F : Type*} [Field F] [CharP F 2] [Finite F] :
    Odd (Nat.card ↥(Work.Models.PSL2.D (F := F))) := by
  haveI : Fintype F := Fintype.ofFinite F
  rw [card_D (F := F)]
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  rw [hcard]
  exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (PNat.ne_zero n)) odd_one

/-- The standard Borel of `SL(2,F)` has **even** order: it contains the unipotent radical
`U` of order `|F| = 2^n`. -/
theorem even_card_B {F : Type*} [Field F] [CharP F 2] [Finite F] :
    Even (Nat.card ↥(Work.Models.PSL2.B (F := F))) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hdvd : Nat.card F ∣ Nat.card ↥(B (F := F)) := by
    rw [← card_U (F := F)]
    exact Subgroup.card_dvd_of_le (U_le_B (F := F))
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hev : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact even_two.pow_of_ne_zero (PNat.ne_zero n)
  exact even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hev) hdvd)

/-! ## The two-point stabiliser of an element outside `B` -/

/-- **The Bruhat transport of the two-point stabiliser.**  If `g ∉ B`, then writing
`g = b₁ w b₂` (`b₁, b₂ ∈ B`) by the Bruhat decomposition, conjugation by `b₁` identifies
`B ⊓ B^g` with `B ⊓ B^w = D`: indeed `B^{b₁ w b₂} = (B^w)^{b₁}` because `b₂` normalises `B`,
and `B^{b₁} = B`. -/
lemma exists_conj_D_of_notMem {F : Type*} [Field F] [CharP F 2] {g : SL2 F}
    (hg : g ∉ B (F := F)) :
    ∃ b ∈ B (F := F),
      B (F := F) ⊓ (B (F := F)).map (MulAut.conj g).toMonoidHom
        = (D (F := F)).map (MulAut.conj b).toMonoidHom := by
  rcases bruhat (F := F) g with hB | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact absurd hB hg
  · refine ⟨b₁, hb₁, ?_⟩
    have h₁ : (B (F := F)).map (MulAut.conj b₁).toMonoidHom = B (F := F) :=
      conj_self_of_mem_normalizer (Subgroup.le_normalizer hb₁)
    have h₂ : (B (F := F)).map (MulAut.conj b₂).toMonoidHom = B (F := F) :=
      conj_self_of_mem_normalizer (Subgroup.le_normalizer hb₂)
    -- conjugation by `b₁ * w * b₂` is `conj b₁ ∘ conj w ∘ conj b₂`
    have hcg' : Submission.Blueprint.conj (b₁ * w (F := F) * b₂) (B (F := F))
        = Submission.Blueprint.conj b₁
            (Submission.Blueprint.conj (w (F := F)) (B (F := F))) := by
      rw [conj_mul, conj_mul]
      exact congrArg
        (fun X => Submission.Blueprint.conj b₁
          (Submission.Blueprint.conj (w (F := F)) X)) h₂
    have hcg : (B (F := F)).map (MulAut.conj (b₁ * w (F := F) * b₂)).toMonoidHom
        = ((B (F := F)).map (MulAut.conj (w (F := F))).toMonoidHom).map
            (MulAut.conj b₁).toMonoidHom := hcg'
    have hstep : B (F := F) ⊓
          ((B (F := F)).map (MulAut.conj (w (F := F))).toMonoidHom).map
            (MulAut.conj b₁).toMonoidHom
        = (B (F := F)).map (MulAut.conj b₁).toMonoidHom ⊓
          ((B (F := F)).map (MulAut.conj (w (F := F))).toMonoidHom).map
            (MulAut.conj b₁).toMonoidHom := by
      rw [h₁]
    have hkey : (B (F := F)).map (MulAut.conj b₁).toMonoidHom ⊓
          ((B (F := F)).map (MulAut.conj (w (F := F))).toMonoidHom).map
            (MulAut.conj b₁).toMonoidHom
        = (D (F := F)).map (MulAut.conj b₁).toMonoidHom := by
      rw [← Subgroup.map_inf (B (F := F))
          ((B (F := F)).map (MulAut.conj (w (F := F))).toMonoidHom)
          (MulAut.conj b₁).toMonoidHom (MulAut.conj b₁).injective, inf_conj_w]
    rw [hcg, hstep, hkey]

/-! ## The theorem -/

theorem B_stronglyEmbedded {F : Type*} [Field F] [CharP F 2] [Finite F] :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded (Work.Models.PSL2.B (F := F)) := by
  refine ⟨?_, even_card_B, ?_⟩
  · intro htop
    have hw : w (F := F) ∈ B (F := F) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (w_facts (F := F)).1 hw
  · intro g hg
    obtain ⟨b, -, hb⟩ := exists_conj_D_of_notMem hg
    rw [hb, Subgroup.card_map_of_injective (f := (MulAut.conj b).toMonoidHom)
      (MulAut.conj b).injective]
    exact odd_card_D

end Work.Models.PSL2
