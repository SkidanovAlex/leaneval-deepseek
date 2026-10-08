import Mathlib
import Submission.Work.Frobenius.Complement.ord_mod_eq_prime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Frobenius.Complement

/-!
# The `p`-`q` lemma for a fixed-point-free module

If `T` of order `q` acts on a finite-dimensional module `W` without nonzero fixed points and
`X` of order `p` satisfies `X * T = T ^ s * X` with `s % q ≠ 1`, then `X` has a nonzero fixed
vector.  The proof extends scalars to the algebraic closure, where `T` is diagonalisable; the
eigenvalue of `T` is moved around by `X` in an orbit of length `p`, and the sum of the orbit
of an eigenvector is a nonzero `X`-fixed vector.
-/

/-- In a monoid, if `X * T = T ^ s * X` then `X * T ^ m = T ^ (m * s) * X`. -/
private theorem mul_pow_conj {M : Type*} [Monoid M] {T X : M} {s : ℕ}
    (h : X * T = T ^ s * X) (m : ℕ) : X * T ^ m = T ^ (m * s) * X := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc X * T ^ (m + 1) = (X * T ^ m) * T := by rw [pow_succ, ← mul_assoc]
      _ = (T ^ (m * s) * X) * T := by rw [ih]
      _ = T ^ (m * s) * (X * T) := by rw [mul_assoc]
      _ = T ^ (m * s) * (T ^ s * X) := by rw [h]
      _ = (T ^ (m * s) * T ^ s) * X := by rw [mul_assoc]
      _ = T ^ (m * s + s) * X := by rw [← pow_add]
      _ = T ^ ((m + 1) * s) * X := by rw [Nat.succ_mul]

/-- In a monoid, if `X * T = T ^ s * X` then `X ^ k * T = T ^ (s ^ k) * X ^ k`. -/
private theorem pow_conj {M : Type*} [Monoid M] {T X : M} {s : ℕ}
    (h : X * T = T ^ s * X) (k : ℕ) : X ^ k * T = T ^ (s ^ k) * X ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc X ^ (k + 1) * T = X * (X ^ k * T) := by rw [pow_succ', mul_assoc]
      _ = X * (T ^ (s ^ k) * X ^ k) := by rw [ih]
      _ = (X * T ^ (s ^ k)) * X ^ k := by rw [mul_assoc]
      _ = (T ^ (s ^ k * s) * X) * X ^ k := by rw [mul_pow_conj h (s ^ k)]
      _ = T ^ (s ^ k * s) * (X * X ^ k) := by rw [mul_assoc]
      _ = T ^ (s ^ k * s) * X ^ (k + 1) := by rw [← pow_succ']
      _ = T ^ (s ^ (k + 1)) * X ^ (k + 1) := by rw [← pow_succ]

/-- In a monoid, if `a * b = b * a ^ s` then `a * b ^ k = b ^ k * a ^ (s ^ k)`. -/
private theorem mul_pow_of_conj {M : Type*} [Monoid M] {a b : M} {s : ℕ}
    (h : a * b = b * a ^ s) (k : ℕ) : a * b ^ k = b ^ k * a ^ (s ^ k) := by
  have key : ∀ n : ℕ, a ^ n * b = b * a ^ (n * s) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) * b = a ^ n * (a * b) := by rw [pow_succ, mul_assoc]
        _ = a ^ n * (b * a ^ s) := by rw [h]
        _ = (a ^ n * b) * a ^ s := by rw [mul_assoc]
        _ = (b * a ^ (n * s)) * a ^ s := by rw [ih]
        _ = b * (a ^ (n * s) * a ^ s) := by rw [mul_assoc]
        _ = b * a ^ (n * s + s) := by rw [← pow_add]
        _ = b * a ^ ((n + 1) * s) := by rw [Nat.succ_mul]
  induction k with
  | zero => simp
  | succ k ih =>
    calc a * b ^ (k + 1) = (a * b ^ k) * b := by rw [pow_succ, ← mul_assoc]
      _ = (b ^ k * a ^ (s ^ k)) * b := by rw [ih]
      _ = b ^ k * (a ^ (s ^ k) * b) := by rw [mul_assoc]
      _ = b ^ k * (b * a ^ (s ^ k * s)) := by rw [key (s ^ k)]
      _ = (b ^ k * b) * a ^ (s ^ k * s) := by rw [mul_assoc]
      _ = b ^ (k + 1) * a ^ (s ^ k * s) := by rw [← pow_succ]
      _ = b ^ (k + 1) * a ^ (s ^ (k + 1)) := by rw [← pow_succ]

/-- Arithmetic: if `q` is prime, `q ∣ s ^ p - 1` and `q ∤ s - 1` (`p` prime) then the powers
`s ^ i`, `s ^ j` are distinct modulo `q` for `i < j < p`. -/
private theorem pow_mod_ne_of_lt {p q s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hsp : q ∣ s ^ p - 1) (hs : ¬ q ∣ s - 1)
    {i j : ℕ} (hij : i < j) (hj : j < p) : s ^ i % q ≠ s ^ j % q := by
  have hs0 : s ≠ 0 := by rintro rfl; exact hs (by simp)
  have hspos : 0 < s := Nat.pos_of_ne_zero hs0
  have hqnots : ¬ q ∣ s := by
    intro hqs
    have h1 : q ∣ s ^ p := dvd_pow hqs hp.pos.ne'
    have h2 : q ∣ s ^ p - (s ^ p - 1) := Nat.dvd_sub h1 hsp
    have h3 : s ^ p - (s ^ p - 1) = 1 := by
      have : 1 ≤ s ^ p := Nat.one_le_pow p s hspos
      omega
    rw [h3] at h2
    exact hq.not_dvd_one h2
  intro h
  have hle : s ^ i ≤ s ^ j := Nat.pow_le_pow_right hspos hij.le
  have hdvd : q ∣ s ^ j - s ^ i := (Nat.modEq_iff_dvd' hle).mp h
  have hfac : s ^ j - s ^ i = s ^ i * (s ^ (j - i) - 1) := by
    have hji : j = i + (j - i) := (Nat.add_sub_of_le hij.le).symm
    rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add, ← hji]
  rw [hfac] at hdvd
  have hk : q ∣ s ^ (j - i) - 1 := by
    rcases hq.dvd_mul.mp hdvd with h' | h'
    · exact absurd (hq.dvd_of_dvd_pow h') hqnots
    · exact h'
  have hlt : j - i < p := by omega
  have hpos : 0 < j - i := by omega
  have := Nat.le_of_dvd hpos (ord_mod_eq_prime hp hq hsp hs hk)
  omega

/-- Core lemma, over an algebraically closed field. -/
private theorem exists_fixed_of_isAlgClosed {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    {p q s : ℕ} (hp : p.Prime) (hq : q.Prime) (hs : s % q ≠ 1)
    {T X : V →ₗ[K] V} (hTq : T ^ q = 1) (hT1 : ∀ w, T w = w → w = 0)
    (hXp : X ^ p = 1) (hrel : ∀ w, X (T w) = (T ^ s) (X w)) :
    ∃ w : V, w ≠ 0 ∧ X w = w := by
  classical
  have hppos : 0 < p := hp.pos
  have hTne : T ≠ 1 := by
    intro hT
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    exact hw (hT1 w (by rw [hT]; rfl))
  have hT1inj : Function.Injective (T - 1 : V →ₗ[K] V) := by
    intro a b hab
    have h : T (a - b) = a - b := by
      have h2 : (T - 1 : V →ₗ[K] V) (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have h3 : T (a - b) - (a - b) = 0 := by simpa using h2
      exact sub_eq_zero.mp h3
    exact sub_eq_zero.mp (hT1 (a - b) h)
  have hXinj : Function.Injective X := by
    have hZX : X ^ (p - 1) * X = 1 := by
      rw [← pow_succ X (p - 1), show p - 1 + 1 = p by omega, hXp]
    intro a b hab
    have ha : (X ^ (p - 1) * X) a = (X ^ (p - 1) * X) b := by
      simp only [Module.End.mul_apply, hab]
    rw [hZX] at ha
    simpa using ha
  have hrel' : X * T = T ^ s * X := by
    ext w
    simpa [Module.End.mul_apply] using hrel w
  have hs0 : s ≠ 0 := by
    intro hs0
    have hTs : T ^ s = 1 := by rw [hs0, pow_zero]
    have hT1' : T = 1 := by
      ext w
      show T w = w
      apply hXinj
      rw [hrel w, hTs, Module.End.one_apply]
    exact hTne hT1'
  have hspos : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
  have hsnd : ¬ q ∣ s - 1 := by
    intro hd
    have hmod : 1 ≡ s [MOD q] := (Nat.modEq_iff_dvd' hspos).mpr hd
    have hmod' : 1 % q = s % q := hmod
    have h1q : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
    rw [h1q] at hmod'
    exact hs hmod'.symm
  have hordT : orderOf T = q := by
    have hdvd : orderOf T ∣ q := orderOf_dvd_of_pow_eq_one hTq
    rcases hq.eq_one_or_self_of_dvd (orderOf T) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hTne
    · exact h
  have hsp : q ∣ s ^ p - 1 := by
    have hp1 : 1 ≤ s ^ p := Nat.one_le_pow p s (by omega)
    have hTsp : T ^ (s ^ p) = T := by
      have h := pow_conj hrel' p
      rw [hXp, one_mul, mul_one] at h
      exact h.symm
    have hisT : IsOfFinOrder T := isOfFinOrder_iff_pow_eq_one.mpr ⟨q, hq.pos, hTq⟩
    have hmod : s ^ p ≡ 1 [MOD orderOf T] :=
      (IsOfFinOrder.pow_eq_pow_iff_modEq hisT).mp (by rw [hTsp, pow_one])
    rw [hordT] at hmod
    exact (Nat.modEq_iff_dvd' hp1).mp hmod.symm
  -- eigenvalue of `T`
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  rw [Module.End.hasEigenvalue_iff] at hc
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  have hv : T v = c • v := Module.End.mem_eigenspace_iff.mp hv_mem
  have hpow : ∀ k : ℕ, (T ^ k) v = c ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, ← pow_succ]
  have hcq : c ^ q = 1 := by
    have h1 := hpow q
    rw [hTq] at h1
    simp only [Module.End.one_apply] at h1
    have h2 : c ^ q • v = (1 : K) • v := by rw [one_smul]; exact h1.symm
    exact smul_left_injective K hv_ne h2
  have hc_ne_one : c ≠ 1 := by
    intro hc1
    have hTv : T v = v := by rw [hv, hc1, one_smul]
    have hzero : (T - 1 : V →ₗ[K] V) v = 0 := by
      rw [LinearMap.sub_apply, hTv, Module.End.one_apply, sub_self]
    exact hv_ne (hT1inj (by rw [hzero, map_zero]))
  have hord : orderOf c = q := by
    have hdvd : orderOf c ∣ q := orderOf_dvd_of_pow_eq_one hcq
    rcases hq.eq_one_or_self_of_dvd (orderOf c) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc_ne_one
    · exact h
  -- `Y = X⁻¹`
  set Y : V →ₗ[K] V := X ^ (p - 1) with hYdef
  have hXY : X * Y = 1 := by
    rw [hYdef, ← pow_succ' X (p - 1), show p - 1 + 1 = p by omega, hXp]
  have hYX : Y * X = 1 := by
    rw [hYdef, ← pow_succ X (p - 1), show p - 1 + 1 = p by omega, hXp]
  have hYp : Y ^ p = 1 := by
    rw [hYdef, ← pow_mul, Nat.mul_comm (p - 1) p, pow_mul, hXp, one_pow]
  have hTY : T * Y = Y * T ^ s := by
    have h1 : T = Y * T ^ s * X := by
      have h2 : Y * (X * T) = Y * (T ^ s * X) := by rw [hrel']
      rw [← mul_assoc, hYX, one_mul, ← mul_assoc] at h2
      exact h2
    calc T * Y = (Y * T ^ s * X) * Y := by conv_lhs => rw [h1]
      _ = Y * T ^ s * (X * Y) := by rw [mul_assoc]
      _ = Y * T ^ s * 1 := by rw [hXY]
      _ = Y * T ^ s := by rw [mul_one]
  have hTYi : ∀ i : ℕ, T * Y ^ i = Y ^ i * T ^ (s ^ i) := fun i => mul_pow_of_conj hTY i
  -- the orbit sum
  set Λ : V →ₗ[K] V := ∑ i ∈ Finset.range p, Y ^ i with hΛdef
  have hYΛ : Y * Λ = Λ := by
    have h : (Y - 1 : V →ₗ[K] V) * Λ = 0 := by
      have h1 : (Y - 1 : V →ₗ[K] V) * Λ = ∑ i ∈ Finset.range p, (Y - 1) * Y ^ i := by
        rw [hΛdef, Finset.mul_sum]
      rw [h1]
      trans ∑ i ∈ Finset.range p, (Y ^ (i + 1) - Y ^ i)
      · exact Finset.sum_congr rfl (fun i _ => by rw [sub_mul, one_mul, ← pow_succ'])
      rw [Finset.sum_range_sub, hYp, pow_zero, sub_self]
    have h3 : Y * Λ - Λ = 0 := by
      rw [sub_mul, one_mul] at h
      exact h
    exact sub_eq_zero.mp h3
  have hXΛ : X * Λ = Λ :=
    calc X * Λ = X * (Y * Λ) := by rw [hYΛ]
      _ = (X * Y) * Λ := by rw [mul_assoc]
      _ = 1 * Λ := by rw [hXY]
      _ = Λ := by rw [one_mul]
  -- the map `i ↦ c ^ (s ^ i)` is injective on `Fin p`
  have hμ_inj : Function.Injective (fun i : Fin p => c ^ (s ^ (i : ℕ))) := by
    intro i j hij
    by_contra hne
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
    have hisc : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr ⟨q, hq.pos, hcq⟩
    have hmod : s ^ (i : ℕ) ≡ s ^ (j : ℕ) [MOD orderOf c] :=
      (IsOfFinOrder.pow_eq_pow_iff_modEq hisc).mp hij
    rw [hord] at hmod
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · exact pow_mod_ne_of_lt hp hq hsp hsnd hlt j.isLt hmod
    · exact pow_mod_ne_of_lt hp hq hsp hsnd hlt i.isLt hmod.symm
  have heig : ∀ i : Fin p, Module.End.HasEigenvector T (c ^ (s ^ (i : ℕ))) ((Y ^ (i : ℕ)) v) := by
    intro i
    rw [Module.End.hasEigenvector_iff]
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      have h1 : T ((Y ^ (i : ℕ)) v) = (Y ^ (i : ℕ)) ((T ^ (s ^ (i : ℕ))) v) := by
        rw [← Module.End.mul_apply, hTYi (i : ℕ), Module.End.mul_apply]
      rw [h1, hpow (s ^ (i : ℕ)), map_smul]
    · intro h0
      have hcomm : Commute X Y := by
        rw [hYdef]
        exact (Commute.refl X).pow_right (p - 1)
      have h1 : X ^ (i : ℕ) * Y ^ (i : ℕ) = 1 := by
        rw [← hcomm.mul_pow, hXY, one_pow]
      have h2 : (X ^ (i : ℕ) * Y ^ (i : ℕ)) v = v := by rw [h1]; rfl
      rw [Module.End.mul_apply, h0, map_zero] at h2
      exact hv_ne h2.symm
  have hLI : LinearIndependent K (fun i : Fin p => (Y ^ (i : ℕ)) v) :=
    Module.End.eigenvectors_linearIndependent' T
      (fun i : Fin p => c ^ (s ^ (i : ℕ))) hμ_inj _ heig
  have hsum_ne : (∑ i : Fin p, (Y ^ (i : ℕ)) v) ≠ 0 := by
    intro h0
    have h0' : ∑ i : Fin p, (1 : K) • (Y ^ (i : ℕ)) v = 0 := by simpa using h0
    have h1 := (Fintype.linearIndependent_iff.mp hLI (fun _ : Fin p => (1 : K))) h0'
    exact one_ne_zero (h1 ⟨0, hp.pos⟩)
  have hsum_eq : (∑ i ∈ Finset.range p, Y ^ i) v = ∑ i : Fin p, (Y ^ (i : ℕ)) v := by
    rw [LinearMap.sum_apply, Fin.sum_univ_eq_sum_range (fun i => (Y ^ i) v) p]
  have hΛv_ne : Λ v ≠ 0 := by
    rw [hΛdef, hsum_eq]
    exact hsum_ne
  exact ⟨Λ v, hΛv_ne, by rw [← Module.End.mul_apply, hXΛ]⟩

theorem exists_fixed_of_isFpf_module {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] [Nontrivial W] {p q s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpF : (p : F) ≠ 0) (hqF : (q : F) ≠ 0) (hs : s % q ≠ 1)
    {T X : W →ₗ[F] W} (hTq : T ^ q = 1) (hT1 : ∀ w, T w = w → w = 0)
    (hXp : X ^ p = 1) (hrel : ∀ w, X (T w) = (T ^ s) (X w)) :
    ∃ w : W, w ≠ 0 ∧ X w = w := by
  classical
  haveI : Module.Flat F (AlgebraicClosure F) := inferInstance
  have baseChange_inj : ∀ (f : W →ₗ[F] W), Function.Injective f →
      Function.Injective (LinearMap.baseChange (AlgebraicClosure F) f) := by
    intro f hf
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f hf
  -- hypotheses for the base-changed operators
  set T' : (TensorProduct F (AlgebraicClosure F) W) →ₗ[AlgebraicClosure F]
      (TensorProduct F (AlgebraicClosure F) W) :=
    LinearMap.baseChange (AlgebraicClosure F) T with hT'def
  set X' : (TensorProduct F (AlgebraicClosure F) W) →ₗ[AlgebraicClosure F]
      (TensorProduct F (AlgebraicClosure F) W) :=
    LinearMap.baseChange (AlgebraicClosure F) X with hX'def
  have hTq' : T' ^ q = 1 := by
    rw [hT'def, ← LinearMap.baseChange_pow, hTq, LinearMap.baseChange_one]
  have hXp' : X' ^ p = 1 := by
    rw [hX'def, ← LinearMap.baseChange_pow, hXp, LinearMap.baseChange_one]
  have hT1inj : Function.Injective (T - 1 : W →ₗ[F] W) := by
    intro a b hab
    have h : T (a - b) = a - b := by
      have h2 : (T - 1 : W →ₗ[F] W) (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have h3 : T (a - b) - (a - b) = 0 := by simpa using h2
      exact sub_eq_zero.mp h3
    exact sub_eq_zero.mp (hT1 (a - b) h)
  have hT1' : ∀ w, T' w = w → w = 0 := by
    intro w hw
    have h2 : T' - 1 = LinearMap.baseChange (AlgebraicClosure F) (T - 1) := by
      rw [hT'def, LinearMap.baseChange_sub, LinearMap.baseChange_one]
    have h3 : (T' - 1 : _ →ₗ[AlgebraicClosure F] _) w = 0 := by
      rw [LinearMap.sub_apply, hw, Module.End.one_apply, sub_self]
    rw [h2] at h3
    exact baseChange_inj (T - 1) hT1inj (by rw [h3, map_zero])
  have hrel' : ∀ w, X' (T' w) = (T' ^ s) (X' w) := by
    intro w
    have h2 : X' * T' = T' ^ s * X' := by
      rw [hX'def, hT'def, ← LinearMap.baseChange_pow]
      rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul]
      congr 1
      ext z
      simpa [Module.End.mul_apply] using hrel z
    rw [← Module.End.mul_apply, h2, Module.End.mul_apply]
  obtain ⟨u, hu_ne, hu_fix⟩ :=
    exists_fixed_of_isAlgClosed (K := AlgebraicClosure F)
      (V := TensorProduct F (AlgebraicClosure F) W) hp hq hs hTq' hT1' hXp' hrel'
  -- descend
  have hnotinj : ¬ Function.Injective (X - 1 : W →ₗ[F] W) := by
    intro hinj
    have hinj' : Function.Injective (LinearMap.baseChange (AlgebraicClosure F) (X - 1)) :=
      baseChange_inj (X - 1) hinj
    have h2 : X' - 1 = LinearMap.baseChange (AlgebraicClosure F) (X - 1) := by
      rw [hX'def, LinearMap.baseChange_sub, LinearMap.baseChange_one]
    have h1 : (X' - 1 : _ →ₗ[AlgebraicClosure F] _) u = 0 := by
      rw [LinearMap.sub_apply, hu_fix, Module.End.one_apply, sub_self]
    rw [h2] at h1
    exact hu_ne (hinj' (by rw [h1, map_zero]))
  rw [← LinearMap.ker_eq_bot] at hnotinj
  obtain ⟨w, hwmem, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnotinj
  refine ⟨w, hwne, ?_⟩
  rw [LinearMap.mem_ker] at hwmem
  have : X w - w = 0 := by simpa using hwmem
  exact sub_eq_zero.mp this

end Work.Frobenius.Complement
