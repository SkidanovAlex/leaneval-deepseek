import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

namespace Commons.LinearAlgebra.Submodule

open Module

noncomputable section

/-- The product `∏_{i<m} (q^n - q^i)`, counting the ordered linearly independent `m`-tuples
in an `n`-dimensional vector space over a field with `q` elements. -/
private def qP (q n m : ℕ) : ℕ := ∏ i : Fin m, (q ^ n - q ^ i.val)

/-- The product `∏_{i<m} (q^m - q^i)`, counting the ordered bases of an `m`-dimensional
vector space over a field with `q` elements. -/
private def qF (q m : ℕ) : ℕ := ∏ i : Fin m, (q ^ m - q ^ i.val)

private lemma qF_succ (q m : ℕ) : qF q (m + 1) = (q ^ (m + 1) - 1) * q ^ m * qF q m := by
  unfold qF
  rw [Fin.prod_univ_succ]
  have h0 : q ^ (m + 1) - q ^ (0 : Fin (m + 1)).val = q ^ (m + 1) - 1 := by simp
  rw [h0]
  have hterm : ∀ i : Fin m, q ^ (m + 1) - q ^ (i.succ).val = q * (q ^ m - q ^ i.val) := by
    intro i
    rw [Fin.val_succ, Nat.mul_sub_left_distrib, ← pow_succ', ← pow_succ']
  rw [Finset.prod_congr rfl (fun i _ => hterm i)]
  rw [Finset.prod_mul_distrib]
  rw [show (∏ _i : Fin m, q) = q ^ m by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
  ring

private lemma qP_succ (q n m : ℕ) : qP q n (m + 1) = (q ^ n - q ^ m) * qP q n m := by
  unfold qP
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [mul_comm]

private lemma qF_pos {q m : ℕ} (hq : 1 < q) : 0 < qF q m := by
  unfold qF
  apply Finset.prod_pos
  intro i _
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq i.isLt)

private lemma qP_pos {q n m : ℕ} (hq : 1 < q) (hm : m ≤ n) : 0 < qP q n m := by
  unfold qP
  apply Finset.prod_pos
  intro i _
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq (lt_of_lt_of_le i.isLt hm))

private theorem gaussian_strictMono {q n m : ℕ} (hq : 1 < q) (hm : 2 * m + 2 ≤ n)
    (N : ℕ → ℕ) (hN : ∀ k, k ≤ n → N k * qF q k = qP q n k) : N m < N (m + 1) := by
  have hle : m + 1 ≤ n := by omega
  have hle' : m ≤ n := by omega
  have hA := hN m hle'
  have hB := hN (m + 1) hle
  suffices hkey : qP q n m * qF q (m + 1) < qP q n (m + 1) * qF q m by
    have hc : N m * (qF q m * qF q (m + 1)) < N (m + 1) * (qF q m * qF q (m + 1)) := by
      calc N m * (qF q m * qF q (m + 1))
          = (N m * qF q m) * qF q (m + 1) := by ac_rfl
        _ = qP q n m * qF q (m + 1) := by rw [hA]
        _ < qP q n (m + 1) * qF q m := hkey
        _ = (N (m + 1) * qF q (m + 1)) * qF q m := by rw [hB]
        _ = N (m + 1) * (qF q m * qF q (m + 1)) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_right hc
  have hnm : m ≤ n := by omega
  have hcore : (q ^ (m + 1) - 1) * q ^ m < q ^ n - q ^ m := by
    have h1 : q ^ n - q ^ m = q ^ m * (q ^ (n - m) - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, mul_comm (q ^ m) (q ^ (n - m)),
        Nat.pow_sub_mul_pow q hnm]
    rw [h1, mul_comm (q ^ m) (q ^ (n - m) - 1)]
    apply Nat.mul_lt_mul_of_pos_right _ (pow_pos (by omega : 0 < q) m)
    have hlt : m + 1 < n - m := by omega
    have hp : q ^ (m + 1) < q ^ (n - m) := Nat.pow_lt_pow_right hq hlt
    exact Nat.sub_lt_sub_right (Nat.one_le_pow (m + 1) q (by omega)) hp
  calc qP q n m * qF q (m + 1)
      = qP q n m * ((q ^ (m + 1) - 1) * q ^ m * qF q m) := by rw [qF_succ]
    _ = ((q ^ (m + 1) - 1) * q ^ m) * (qP q n m * qF q m) := by ac_rfl
    _ < (q ^ n - q ^ m) * (qP q n m * qF q m) :=
        Nat.mul_lt_mul_of_pos_right hcore (Nat.mul_pos (qP_pos hq hnm) (qF_pos hq))
    _ = ((q ^ n - q ^ m) * qP q n m) * qF q m := by ac_rfl
    _ = qP q n (m + 1) * qF q m := by rw [qP_succ]

private lemma linearIndependent_coe_subtype {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {m : ℕ} {W : Submodule K V} {g : Fin m → ↥W}
    (hg : LinearIndependent K g) : LinearIndependent K (fun i => (g i : V)) :=
  hg.map' (Submodule.subtype W) (Submodule.ker_subtype W)

private noncomputable def spanFiberEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (m : ℕ) (W : Submodule K V) (hW : Module.finrank K W = m) :
    {f : Fin m → V // LinearIndependent K f ∧
        Submodule.span K (Set.range f) = W} ≃
      {g : Fin m → ↥W // LinearIndependent K g} where
  toFun F :=
    ⟨fun i => ⟨F.1 i, by
        have h : F.1 i ∈ Submodule.span K (Set.range F.1) := Submodule.subset_span ⟨i, rfl⟩
        rwa [F.2.2] at h⟩,
      LinearIndependent.of_comp (Submodule.subtype W) (by
        convert F.2.1 using 1
        funext i
        rfl)⟩
  invFun g :=
    ⟨fun i => ((g : Fin m → ↥W) i : V), linearIndependent_coe_subtype g.2, by
      have hle : Submodule.span K (Set.range (fun i => ((g : Fin m → ↥W) i : V))) ≤ W := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact ((g : Fin m → ↥W) i).2
      have hdim : Module.finrank K
          ↥(Submodule.span K (Set.range (fun i => ((g : Fin m → ↥W) i : V)))) =
          Module.finrank K ↥W := by
        rw [finrank_span_eq_card (linearIndependent_coe_subtype g.2), hW, Fintype.card_fin]
      exact Submodule.eq_of_le_of_finrank_eq hle hdim⟩
  left_inv F := by
    apply Subtype.ext
    funext i
    rfl
  right_inv g := by
    apply Subtype.ext
    funext i
    exact Subtype.ext rfl

private theorem card_linearIndependent_eq_sum {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] (m : ℕ) :
    Nat.card {f : Fin m → V // LinearIndependent K f} =
      Nat.card {W : Submodule K V // Module.finrank K W = m} * qF (Fintype.card K) m := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (Submodule K V) :=
    Fintype.ofInjective (fun W : Submodule K V => (W : Set V))
      (fun a b h => SetLike.ext' h)
  let e : {f : Fin m → V // LinearIndependent K f} ≃
      Σ W : {W : Submodule K V // Module.finrank K W = m},
        {f : Fin m → V // LinearIndependent K f ∧ Submodule.span K (Set.range f) = W.1} :=
    { toFun := fun f => ⟨⟨Submodule.span K (Set.range (f : Fin m → V)),
          by rw [finrank_span_eq_card f.2, Fintype.card_fin]⟩,
        ⟨(f : Fin m → V), f.2, rfl⟩⟩
      invFun := fun s => ⟨s.2.1, s.2.2.1⟩
      left_inv := fun f => rfl
      right_inv := fun s => by
        obtain ⟨⟨W, hW⟩, ⟨f, hf, hspan⟩⟩ := s
        refine Sigma.ext (Subtype.ext hspan) ?_
        rw [Subtype.heq_iff_coe_eq (fun x =>
          ⟨fun h => ⟨h.1, h.2.trans hspan⟩, fun h => ⟨h.1, h.2.trans hspan.symm⟩⟩)] }
  have hsum : Nat.card {f : Fin m → V // LinearIndependent K f} =
      ∑ W : {W : Submodule K V // Module.finrank K W = m},
        Nat.card {f : Fin m → V // LinearIndependent K f ∧
          Submodule.span K (Set.range f) = W.1} := by
    rw [Nat.card_congr e, Nat.card_sigma]
  have hfiber : ∀ W : {W : Submodule K V // Module.finrank K W = m},
      Nat.card {f : Fin m → V // LinearIndependent K f ∧
        Submodule.span K (Set.range f) = W.1} = qF (Fintype.card K) m := by
    intro W
    rw [Nat.card_congr (spanFiberEquiv m W.1 W.2)]
    rw [card_linearIndependent (K := K) (V := ↥W.1) (k := m) (by rw [W.2])]
    simp only [qF]
    rw [W.2]
  rw [hsum, Finset.sum_congr rfl (fun W _ => hfiber W), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]

private theorem card_submodule_finrank_count {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] (m : ℕ)
    (hm : m ≤ Module.finrank K V) :
    Nat.card {W : Submodule K V // Module.finrank K W = m} * qF (Fintype.card K) m =
      qP (Fintype.card K) (Module.finrank K V) m := by
  haveI : Finite V := Module.finite_of_finite K
  rw [← card_linearIndependent_eq_sum (K := K) (V := V) m]
  rw [card_linearIndependent (K := K) (V := V) (k := m) hm]
  simp only [qP]

theorem card_submodule_finrank_strictMono {K V : Type*} [Field K] [Fintype K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {m : ℕ} (h : 2 * m + 2 ≤ Module.finrank K V) :
    Nat.card {W : Submodule K V // Module.finrank K W = m} <
      Nat.card {W : Submodule K V // Module.finrank K W = m + 1} := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  exact gaussian_strictMono hq h
    (fun k => Nat.card {W : Submodule K V // Module.finrank K W = k})
    (fun k hk => card_submodule_finrank_count (K := K) (V := V) k hk)

end

end Commons.LinearAlgebra.Submodule