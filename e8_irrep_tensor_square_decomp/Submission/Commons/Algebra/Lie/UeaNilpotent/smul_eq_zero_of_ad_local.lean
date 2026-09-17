import Mathlib
import Submission.Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota

open Finset

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace Commons.Algebra.Lie.UeaNilpotent

section RingAux

variable {A : Type*} [Ring A]

private lemma nsmul_mul_ring (a : A) (c : ℕ) (b : A) : (c • a) * b = c • (a * b) := by
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_assoc]

private lemma mul_nsmul_ring (z w : A) (c : ℕ) : z * (c • w) = c • (z * w) := by
  rw [nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_comm c z, mul_assoc]

private lemma sub_mul_sub_mul_add (z a b : A) :
    z * (a + b) - (a + b) * z = (z * a - a * z) + (z * b - b * z) := by
  rw [mul_add, add_mul]; abel

private lemma sub_mul_sub_mul_mul (z a b : A) :
    z * (a * b) - (a * b) * z = (z * a - a * z) * b + a * (z * b - b * z) := by
  noncomm_ring

private lemma sub_mul_sub_mul_nsmul (z a : A) (c : ℕ) :
    z * (c • a) - (c • a) * z = c • (z * a - a * z) := by
  rw [mul_nsmul_ring, nsmul_mul_ring, ← smul_sub]

private lemma sub_mul_sub_mul_sum {ι : Type*} (z : A) (s : Finset ι) (f : ι → A) :
    z * (∑ i ∈ s, f i) - (∑ i ∈ s, f i) * z = ∑ i ∈ s, (z * f i - f i * z) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

private theorem pow_mul_eq_sum_antidiagonal (z u : A) (n : ℕ) :
    z ^ n * u = ∑ ij ∈ antidiagonal n,
      n.choose ij.1 • (Nat.iterate (fun v : A => z * v - v * z) ij.1 u * z ^ ij.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    rw [ih, Finset.mul_sum]
    rw [sum_antidiagonal_choose_succ_nsmul
      (fun i j => Nat.iterate (fun v : A => z * v - v * z) i u * z ^ j) n]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ij hij
    have hz : z * Nat.iterate (fun v : A => z * v - v * z) ij.1 u
        = Nat.iterate (fun v : A => z * v - v * z) (ij.1 + 1) u
          + Nat.iterate (fun v : A => z * v - v * z) ij.1 u * z := by
      rw [Function.iterate_succ_apply']
      abel
    rw [mul_nsmul_ring, ← mul_assoc, hz, add_mul, smul_add]
    rw [← Nat.choose_symm_of_eq_add (HasAntidiagonal.mem_antidiagonal.mp hij).symm]
    rw [add_comm]
    congr 1
    rw [mul_assoc, ← pow_succ']

private theorem iterate_sub_mul_sub_mul (z x y : A) (n : ℕ) :
    (Nat.iterate (fun v : A => z * v - v * z) n) (x * y)
      = ∑ ij ∈ antidiagonal n, n.choose ij.1 •
        ((Nat.iterate (fun v : A => z * v - v * z) ij.1) x
          * (Nat.iterate (fun v : A => z * v - v * z) ij.2) y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, sub_mul_sub_mul_sum]
    rw [sum_antidiagonal_choose_succ_nsmul
      (fun i j => (Nat.iterate (fun v : A => z * v - v * z) i) x
        * (Nat.iterate (fun v : A => z * v - v * z) j) y) n]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ij hij
    rw [mul_nsmul_ring, nsmul_mul_ring, ← smul_sub]
    rw [sub_mul_sub_mul_mul, smul_add]
    rw [← Nat.choose_symm_of_eq_add (HasAntidiagonal.mem_antidiagonal.mp hij).symm]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', add_comm]

end RingAux

section IterAux

private lemma iterate_add_of_add {A : Type*} [AddCommMonoid A] (g : A → A)
    (hg : ∀ a b, g (a + b) = g a + g b) (k : ℕ) (a b : A) :
    (Nat.iterate g k) (a + b) = (Nat.iterate g k) a + (Nat.iterate g k) b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, hg, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

private lemma iterate_eq_zero_of_le {A : Type*} [Zero A] (g : A → A) (hg : g 0 = 0) {a : A} {m : ℕ}
    (hm : (Nat.iterate g m) a = 0) {k : ℕ} (hk : m ≤ k) : (Nat.iterate g k) a = 0 := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  have hstep : (Nat.iterate g k) a = (Nat.iterate g d) ((Nat.iterate g m) a) := by
    rw [hd, Nat.add_comm, Function.iterate_add_apply]
  rw [hstep, hm]
  exact Function.iterate_fixed hg d

end IterAux

private theorem adU_locallyNilpotent {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    (f : L) (hf : ∀ x : L, ∃ n : ℕ, ((LieAlgebra.ad K L f)^n) x = 0) :
    ∀ u : UniversalEnvelopingAlgebra K L, ∃ n : ℕ,
      (Nat.iterate (fun v : UniversalEnvelopingAlgebra K L =>
        UniversalEnvelopingAlgebra.ι K f * v - v * UniversalEnvelopingAlgebra.ι K f) n) u = 0 := by
  let z : UniversalEnvelopingAlgebra K L := UniversalEnvelopingAlgebra.ι K f
  let δ : UniversalEnvelopingAlgebra K L → UniversalEnvelopingAlgebra K L := fun v => z * v - v * z
  have hδ0 : δ 0 = 0 := by simp [δ]
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := fun a b => sub_mul_sub_mul_add z a b
  have hδiota : ∀ w : L, δ (UniversalEnvelopingAlgebra.ι K w)
      = UniversalEnvelopingAlgebra.ι K (LieAlgebra.ad K L f w) := by
    intro w
    have h : ⁅z, UniversalEnvelopingAlgebra.ι K w⁆ = UniversalEnvelopingAlgebra.ι K ⁅f, w⁆ :=
      (LieHom.map_lie (UniversalEnvelopingAlgebra.ι K) f w).symm
    rw [LieRing.of_associative_ring_bracket] at h
    show z * UniversalEnvelopingAlgebra.ι K w - UniversalEnvelopingAlgebra.ι K w * z
      = UniversalEnvelopingAlgebra.ι K (LieAlgebra.ad K L f w)
    rw [h, LieAlgebra.ad_apply]
  have hiter : ∀ (n : ℕ) (w : L),
      (Nat.iterate δ n) (UniversalEnvelopingAlgebra.ι K w)
        = UniversalEnvelopingAlgebra.ι K (((LieAlgebra.ad K L f)^n) w) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', ih, hδiota]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ']
  have hmem : ∀ x ∈ Set.range (UniversalEnvelopingAlgebra.ι K : L → UniversalEnvelopingAlgebra K L),
      ∃ n : ℕ, (Nat.iterate δ n) x = 0 := by
    rintro x ⟨w, rfl⟩
    obtain ⟨n, hn⟩ := hf w
    exact ⟨n, by rw [hiter n w, hn, map_zero]⟩
  have hscalar : ∀ r : K,
      ∃ n : ℕ, (Nat.iterate δ n) (algebraMap K (UniversalEnvelopingAlgebra K L) r) = 0 := by
    intro r
    refine ⟨1, ?_⟩
    show z * algebraMap K (UniversalEnvelopingAlgebra K L) r
      - algebraMap K (UniversalEnvelopingAlgebra K L) r * z = 0
    rw [Algebra.commutes, sub_self]
  have hadd : ∀ x y, (∃ n, (Nat.iterate δ n) x = 0) → (∃ n, (Nat.iterate δ n) y = 0) →
      ∃ n, (Nat.iterate δ n) (x + y) = 0 := by
    rintro x y ⟨m, hm⟩ ⟨k, hk⟩
    refine ⟨max m k, ?_⟩
    rw [iterate_add_of_add δ hδadd (max m k) x y]
    rw [iterate_eq_zero_of_le δ hδ0 hm (le_max_left m k),
        iterate_eq_zero_of_le δ hδ0 hk (le_max_right m k), add_zero]
  have hmul : ∀ x y, (∃ n, (Nat.iterate δ n) x = 0) → (∃ n, (Nat.iterate δ n) y = 0) →
      ∃ n, (Nat.iterate δ n) (x * y) = 0 := by
    rintro x y ⟨m, hm⟩ ⟨k, hk⟩
    refine ⟨m + k, ?_⟩
    change (Nat.iterate (fun v : UniversalEnvelopingAlgebra K L => z * v - v * z) (m + k))
      (x * y) = 0
    rw [iterate_sub_mul_sub_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have hsum : ij.1 + ij.2 = m + k := HasAntidiagonal.mem_antidiagonal.mp hij
    rcases lt_or_ge ij.1 m with hlt | hle
    · have hk' : k ≤ ij.2 := by omega
      rw [iterate_eq_zero_of_le δ hδ0 hk hk', mul_zero, smul_zero]
    · rw [iterate_eq_zero_of_le δ hδ0 hm hle, zero_mul, smul_zero]
  intro u
  have hu : u ∈ Algebra.adjoin K
      (Set.range (UniversalEnvelopingAlgebra.ι K : L → UniversalEnvelopingAlgebra K L)) := by
    rw [Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota]; trivial
  exact Algebra.adjoin_induction (p := fun u _ => ∃ n : ℕ, (Nat.iterate δ n) u = 0)
    hmem hscalar (fun x y _ _ hx hy => hadd x y hx hy) (fun x y _ _ hx hy => hmul x y hx hy) hu


section Main

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module (UniversalEnvelopingAlgebra K L) M]

private lemma iota_pow_smul
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι K x) • m = ⁅x, m⁆)
    (f : L) (m : M) (k : ℕ) :
    ((UniversalEnvelopingAlgebra.ι K f)^k) • m = ((LieModule.toEnd K L M f)^k) m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_smul, ih]
    rw [hι f (((LieModule.toEnd K L M f)^k) m)]
    rw [← LieModule.toEnd_apply_apply K L M f (((LieModule.toEnd K L M f)^k) m)]
    rw [← Module.End.mul_apply, ← pow_succ']

theorem smul_eq_zero_of_ad_local {K L M : Type*} [Field K] [CharZero K] [LieRing L]
    [LieAlgebra K L] [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module (UniversalEnvelopingAlgebra K L) M]
    (hι : ∀ (x : L) (m : M), (UniversalEnvelopingAlgebra.ι K x) • m = ⁅x, m⁆)
    (f : L) (hf : ∀ x : L, ∃ n : ℕ, ((LieAlgebra.ad K L f)^n) x = 0)
    {m : M} (hm : ∃ N : ℕ, ((LieModule.toEnd K L M f)^N) m = 0)
    (u : UniversalEnvelopingAlgebra K L) :
    ∃ N' : ℕ, ((LieModule.toEnd K L M f)^N') (u • m) = 0 := by
  obtain ⟨N, hN⟩ := hm
  obtain ⟨n, hn⟩ := adU_locallyNilpotent (K := K) (L := L) f hf u
  let δ : UniversalEnvelopingAlgebra K L → UniversalEnvelopingAlgebra K L :=
    fun v => UniversalEnvelopingAlgebra.ι K f * v - v * UniversalEnvelopingAlgebra.ι K f
  have hδzero : ∀ i : ℕ, n ≤ i → (Nat.iterate δ i) u = 0 := by
    intro i hi
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    have hstep : (Nat.iterate δ i) u = (Nat.iterate δ d) ((Nat.iterate δ n) u) := by
      rw [hd, Nat.add_comm, Function.iterate_add_apply]
    rw [hstep, hn]
    exact Function.iterate_fixed (by simp [δ]) d
  have hTzero : ∀ j : ℕ, N ≤ j → ((LieModule.toEnd K L M f)^j) m = 0 := by
    intro j hj
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    rw [hd, Nat.add_comm, pow_add, Module.End.mul_apply, hN]
    exact map_zero _
  refine ⟨n + N, ?_⟩
  have hstep : ((LieModule.toEnd K L M f)^(n + N)) (u • m)
      = (((UniversalEnvelopingAlgebra.ι K f)^(n + N)) * u) • m := by
    rw [← iota_pow_smul (hι := hι) f (u • m) (n + N), mul_smul]
  rw [hstep, pow_mul_eq_sum_antidiagonal, Finset.sum_smul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hw : (Nat.iterate (fun v : UniversalEnvelopingAlgebra K L =>
        UniversalEnvelopingAlgebra.ι K f * v - v * UniversalEnvelopingAlgebra.ι K f) ij.1 u
      * (UniversalEnvelopingAlgebra.ι K f)^ij.2) • m = 0 := by
    rw [mul_smul, iota_pow_smul (hι := hι) f m ij.2]
    rcases lt_or_ge ij.1 n with hlt | hge
    · have hij2 : N ≤ ij.2 := by
        have := HasAntidiagonal.mem_antidiagonal.mp hij; omega
      rw [hTzero ij.2 hij2, smul_zero]
    · rw [hδzero ij.1 hge, zero_smul]
  rw [nsmul_eq_mul, mul_smul, hw, smul_zero]

end Main

end Commons.Algebra.Lie.UeaNilpotent
