import Mathlib.Algebra.Order.Ring.Star
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Module

namespace Commons.LinearAlgebra.Submodule

variable {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [Finite V]

/-- The image under `W.subtype` of a linearly independent family spanning a subspace `W`
of dimension `m` is still linearly independent in `V`. -/
private lemma aux_linindep_subtype {W : Submodule K V} {m : ℕ}
    {g : Fin m → W} (hg : LinearIndependent K g) :
    LinearIndependent K (fun i => (g i : V)) :=
  LinearIndependent.map hg (f := Submodule.subtype W) (by
    rw [Submodule.ker_subtype]; exact disjoint_bot_right)

/-- If `W` has dimension `m` and `g : Fin m → W` is linearly independent, then the span of the
image of `g` in `V` is exactly `W`. -/
private lemma span_subtype_range_eq {W : Submodule K V} {m : ℕ} (hW : finrank K W = m)
    {g : Fin m → W} (hg : LinearIndependent K g) :
    Submodule.span K (Set.range (fun i => (g i : V))) = W := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (g i).2
  · rw [finrank_span_eq_card (aux_linindep_subtype hg), Fintype.card_fin, hW]

/-- Map an `m`-dimensional subspace together with a linearly independent `m`-tuple inside it
to the corresponding linearly independent `m`-tuple of `V`. -/
private noncomputable def auxPhi (m : ℕ) :
    (Σ W : {W : Submodule K V // Module.finrank K W = m},
        {v : Fin m → W.1 // LinearIndependent K v}) →
      {v : Fin m → V // LinearIndependent K v} :=
  fun x => ⟨fun i => (x.2.1 i : V), aux_linindep_subtype x.2.2⟩

/-- `auxPhi` is injective: the underlying tuple determines the subspace (as its span) and the
initial linear independent tuple. -/
private lemma auxPhi_injective (m : ℕ) :
    Function.Injective (auxPhi (K := K) (V := V) m) := by
  rintro ⟨⟨W₁,h₁⟩,⟨g₁,hg₁⟩⟩ ⟨⟨W₂,h₂⟩,⟨g₂,hg₂⟩⟩ heq
  have hfun : (fun i => (g₁ i : V)) = (fun i => (g₂ i : V)) := congrArg Subtype.val heq
  have hW : W₁ = W₂ := by
    rw [← span_subtype_range_eq h₁ hg₁, ← span_subtype_range_eq h₂ hg₂, hfun]
  subst hW
  have hg : g₁ = g₂ := by
    funext i
    exact Subtype.ext (congrFun hfun i)
  subst hg
  rfl

/-- The number of linearly independent `m`-tuples inside a subspace `W` of dimension `m`. -/
private lemma card_linindep_of_finrank {m : ℕ}
    (W : {W : Submodule K V // finrank K W = m}) :
    Nat.card {v : Fin m → W.1 // LinearIndependent K v}
      = ∏ i : Fin m, (Nat.card K ^ m - Nat.card K ^ i.val) := by
  rw [card_linearIndependent (K := K) (V := W.1) (k := m) (le_of_eq W.2.symm), W.2]
  simp_rw [← Nat.card_eq_fintype_card]

/-- The number of linearly independent `m`-tuples in `V`. -/
private lemma card_linindep_total {m : ℕ} (hm : m ≤ finrank K V) :
    Nat.card {v : Fin m → V // LinearIndependent K v}
      = ∏ i : Fin m, (Nat.card K ^ finrank K V - Nat.card K ^ i.val) := by
  rw [card_linearIndependent (K := K) (V := V) (k := m) hm]
  simp_rw [← Nat.card_eq_fintype_card]

/-- Double counting: the disjoint union, over all `m`-dimensional subspaces `W`, of the linearly
independent `m`-tuples lying in `W`, has cardinality the number of `m`-dimensional subspaces
times the number of linearly independent `m`-tuples in an `m`-dimensional space. -/
private lemma card_sigma_eq (m : ℕ) :
    Nat.card (Σ W : {W : Submodule K V // finrank K W = m},
        {v : Fin m → W.1 // LinearIndependent K v})
      = Nat.card {W : Submodule K V // finrank K W = m}
        * ∏ i : Fin m, (Nat.card K ^ m - Nat.card K ^ i.val) := by
  haveI : Fintype {W : Submodule K V // finrank K W = m} := Fintype.ofFinite _
  rw [Nat.card_sigma]
  rw [Finset.sum_congr rfl (fun W _ => card_linindep_of_finrank W)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
    ← Nat.card_eq_fintype_card]

/-- Upper bound `∏ᵢ (qⁿ - qⁱ) ≤ q ^ (n * m)`. -/
private lemma prod_upper (m n q : ℕ) :
    ∏ i : Fin m, (q ^ n - q ^ i.val) ≤ q ^ (n * m) := by
  calc ∏ i : Fin m, (q ^ n - q ^ i.val) ≤ ∏ _i : Fin m, q ^ n :=
        Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => Nat.sub_le _ _)
    _ = (q ^ n) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = q ^ (n * m) := by rw [pow_mul]

/-- Lower bound `q ^ (m * (m - 1)) ≤ ∏ᵢ (q^m - qⁱ)` for `q ≥ 2`. -/
private lemma prod_lower (m q : ℕ) (hq : 2 ≤ q) :
    q ^ (m * (m - 1)) ≤ ∏ i : Fin m, (q ^ m - q ^ i.val) := by
  rcases m with _ | k
  · simp
  · have hfac : ∀ i : Fin (k+1), q ^ k ≤ q ^ (k+1) - q ^ i.val := by
      intro i
      have hle : q ^ i.val ≤ q ^ k := by
        apply Nat.pow_le_pow_right (by omega)
        exact Nat.lt_succ_iff.mp i.isLt
      calc q ^ k = q ^ k * 1 := (Nat.mul_one _).symm
        _ ≤ q ^ k * (q - 1) := Nat.mul_le_mul_left _ (by omega)
        _ = q ^ k * q - q ^ k := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        _ = q ^ (k+1) - q ^ k := by rw [pow_succ]
        _ ≤ q ^ (k+1) - q ^ i.val := Nat.sub_le_sub_left hle _
    have hqk : ∏ _i : Fin (k+1), q ^ k = q ^ (k * (k+1)) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    rw [show (k+1) * ((k+1) - 1) = k * (k+1) by rw [Nat.succ_sub_one, Nat.mul_comm], ← hqk]
    exact Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => hfac i)

/-- Arithmetic identity behind the exponent: for `m ≤ n`,
`(m * (n - m) + m) + m * (m - 1) = n * m`. -/
private lemma exp_identity (m n : ℕ) (hm : m ≤ n) :
    (m * (n - m) + m) + m * (m - 1) = n * m := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0; simp
  · rw [← Nat.mul_succ m (n - m), ← Nat.mul_add, Nat.mul_comm n m]
    congr 1
    omega

theorem card_submodule_finrank_le_pow {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [Finite V] (m : ℕ) :
    Nat.card {W : Submodule K V // Module.finrank K W = m}
      ≤ Nat.card K ^ (m * (Module.finrank K V - m) + m) := by
  by_cases hm : m ≤ Module.finrank K V
  · have hq2 : 2 ≤ Nat.card K := by
      have := Fintype.one_lt_card (α := K)
      rw [Nat.card_eq_fintype_card]; omega
    -- Count linear independent `m`-tuples two ways.
    have hKey : Nat.card {W : Submodule K V // Module.finrank K W = m}
          * Nat.card K ^ (m * (m - 1))
        ≤ Nat.card K ^ (Module.finrank K V * m) := by
      calc Nat.card {W : Submodule K V // Module.finrank K W = m}
              * Nat.card K ^ (m * (m - 1))
          ≤ Nat.card {W : Submodule K V // Module.finrank K W = m}
              * ∏ i : Fin m, (Nat.card K ^ m - Nat.card K ^ i.val) :=
            Nat.mul_le_mul_left _ (prod_lower m (Nat.card K) hq2)
        _ = Nat.card (Σ W : {W : Submodule K V // Module.finrank K W = m},
                {v : Fin m → W.1 // LinearIndependent K v}) := (card_sigma_eq m).symm
        _ ≤ Nat.card {v : Fin m → V // LinearIndependent K v} :=
            Nat.card_le_card_of_injective _ (auxPhi_injective m)
        _ = ∏ i : Fin m, (Nat.card K ^ Module.finrank K V - Nat.card K ^ i.val) :=
            card_linindep_total hm
        _ ≤ Nat.card K ^ (Module.finrank K V * m) :=
            prod_upper m (Module.finrank K V) (Nat.card K)
    have hPpos : 0 < Nat.card K ^ (m * (m - 1)) := pow_pos (by omega) _
    have hexp : Nat.card K ^ (Module.finrank K V * m)
        = Nat.card K ^ (m * (Module.finrank K V - m) + m)
            * Nat.card K ^ (m * (m - 1)) := by
      rw [← pow_add, exp_identity m (Module.finrank K V) hm]
    rw [hexp] at hKey
    exact Nat.le_of_mul_le_mul_right hKey hPpos
  · haveI : IsEmpty {W : Submodule K V // Module.finrank K W = m} :=
      ⟨fun W => by have h := Submodule.finrank_le W.1; omega⟩
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

end Commons.LinearAlgebra.Submodule