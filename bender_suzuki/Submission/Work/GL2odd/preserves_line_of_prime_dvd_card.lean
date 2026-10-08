import Mathlib
import Submission.Work.GL2odd.sylow_card_eq_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.GL2odd

open Matrix

noncomputable section

/-! ## Matrix algebra in `M₂(𝔽_p)`

A `2 × 2` matrix `A` over `𝔽_p` (`p` an odd prime) with `A ^ p = 1` is unipotent:
`(A - 1) ^ 2 = 0`.  -/

/-- Cayley–Hamilton for `2 × 2` matrices. -/
private lemma sq_eq_trace_smul_sub_det_smul {p : ℕ} [Fact p.Prime]
    (a : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    a ^ 2 = Matrix.trace a • a - a.det • 1 := by
  rw [pow_two, Matrix.eta_fin_two a]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.sub_apply,
      Matrix.smul_apply]
  all_goals ring

/-- In characteristic `p`, `(X - 1) ^ p = X ^ p - 1`; evaluating at `A` with `A ^ p = 1`
gives `(A - 1) ^ p = 0`. -/
private lemma sub_one_pow_eq_zero {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) (hA : A ^ p = 1) :
    (A - 1) ^ p = 0 := by
  haveI : CharP (Polynomial (ZMod p)) p := inferInstance
  have hpoly : ((Polynomial.X - 1 : Polynomial (ZMod p)) ^ p) = Polynomial.X ^ p - 1 := by
    have h1 : (Polynomial.X - 1 : Polynomial (ZMod p)) = Polynomial.X + (-1) := by ring
    rw [h1, add_pow_char]
    rw [Odd.neg_one_pow hpodd]; ring
  have key : Polynomial.aeval A ((Polynomial.X - 1 : Polynomial (ZMod p)) ^ p) = 0 := by
    rw [hpoly]; simp [Polynomial.aeval_X, hA, map_pow]
  have hAX : Polynomial.aeval A (Polynomial.X - 1 : Polynomial (ZMod p)) = A - 1 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_one]
  rwa [map_pow, hAX] at key

/-- **The matrix core.**  A `2 × 2` matrix over `𝔽_p` (`p` an odd prime) with `A ^ p = 1` and
`A ≠ 1` satisfies `(A - 1) ^ 2 = 0`. -/
private lemma sq_sub_one_eq_zero {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)) (hA : A ^ p = 1) (hne : A ≠ 1) :
    (A - 1) ^ 2 = 0 := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have hNp : (A - 1) ^ p = 0 := sub_one_pow_eq_zero hpodd A hA
  have hdet : (A - 1).det = 0 := by
    have h1 : (A - 1).det ^ p = 0 := by
      rw [← Matrix.det_pow, hNp, Matrix.det_zero]
    exact ((pow_eq_zero_iff').mp h1).1
  have hCH : (A - 1) ^ 2 = Matrix.trace (A - 1) • (A - 1) := by
    rw [sq_eq_trace_smul_sub_det_smul, hdet]; simp
  have hind : ∀ m : ℕ, (A - 1) ^ (m + 1) = (Matrix.trace (A - 1)) ^ m • (A - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ih, Matrix.smul_mul, ← pow_two, hCH, smul_smul, ← pow_succ]
  have hNne : (A - 1) ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have htrp : (Matrix.trace (A - 1)) ^ (p - 1) • (A - 1) = 0 := by
    have h := hind (p - 1)
    rw [show p - 1 + 1 = p from by omega] at h
    rw [← h, hNp]
  have htr : Matrix.trace (A - 1) = 0 := by
    obtain ⟨i, j, hij⟩ : ∃ i j : Fin 2, (A - 1) i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hNne (by ext i j; exact h i j)
    have h1 : (Matrix.trace (A - 1)) ^ (p - 1) * (A - 1) i j = 0 := by
      have h2 := congrFun (congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M i) htrp) j
      simpa [Matrix.smul_apply, Matrix.zero_apply, Pi.zero_apply, smul_eq_mul] using h2
    exact ((pow_eq_zero_iff').mp ((mul_eq_zero.mp h1).resolve_right hij)).1
  rw [hCH, htr, zero_smul]

/-- The `m`-th power of a unipotent `1 + N` with `N ^ 2 = 0`. -/
private lemma one_add_pow_eq {p : ℕ} [Fact p.Prime]
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) (hN2 : N ^ 2 = 0) (m : ℕ) :
    (1 + N) ^ m = 1 + (m : ZMod p) • N := by
  have hNN : N * N = 0 := by rw [← pow_two]; exact hN2
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih]
      have hstep : (1 + (k : ZMod p) • N) * (1 + N) = 1 + ((k : ZMod p) + 1) • N := by
        have h1 : (1 + (k : ZMod p) • N) * (1 + N) = 1 + N + (k : ZMod p) • N := by
          simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, hNN, smul_zero,
            add_zero]
          abel
        rw [h1, add_smul, one_smul]
        abel
      rw [hstep, Nat.cast_succ]

/-! ## The kernel of a nonzero nilpotent `2 × 2` matrix -/

/-- A nonzero `2 × 2` matrix with square zero has a `1`-dimensional kernel, and any fixed
vector generates it. -/
private lemma exists_fixed_vec_of_sq_eq_zero {p : ℕ} [Fact p.Prime]
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) (hN : N ≠ 0) (hN2 : N ^ 2 = 0) :
    ∃ e : Fin 2 → ZMod p, e ≠ 0 ∧ N.mulVec e = 0 ∧
      ∀ w, N.mulVec w = 0 → w ∈ Submodule.span (ZMod p) {e} := by
  classical
  have hf : N.mulVecLin ≠ 0 := by
    intro h
    apply hN
    have hzero : Matrix.toLin' N = 0 := by rw [Matrix.toLin'_apply', h]
    exact Matrix.toLin'.injective (by rw [hzero, map_zero])
  have hf2 : N.mulVecLin.comp N.mulVecLin = 0 := by
    rw [← Matrix.mulVecLin_mul, ← pow_two, hN2, Matrix.mulVecLin_zero]
  have hle : LinearMap.range N.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    have hv := LinearMap.congr_fun hf2 v
    simpa using hv
  have hsum : Module.finrank (ZMod p) ↥(LinearMap.range N.mulVecLin)
      + Module.finrank (ZMod p) ↥(LinearMap.ker N.mulVecLin) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [show Module.finrank (ZMod p) (Fin 2 → ZMod p) = 2 from Module.finrank_fin_fun (ZMod p)] at h
    exact h
  have hlef : Module.finrank (ZMod p) ↥(LinearMap.range N.mulVecLin)
      ≤ Module.finrank (ZMod p) ↥(LinearMap.ker N.mulVecLin) :=
    Submodule.finrank_mono hle
  have hrange_ne : LinearMap.range N.mulVecLin ≠ ⊥ := by
    intro h
    exact hf (LinearMap.range_eq_bot.mp h)
  have hpos : 0 < Module.finrank (ZMod p) ↥(LinearMap.range N.mulVecLin) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hrange_ne (Submodule.finrank_eq_zero.mp h0)
  have hfr : Module.finrank (ZMod p) ↥(LinearMap.range N.mulVecLin) = 1 := by omega
  have hfk : Module.finrank (ZMod p) ↥(LinearMap.ker N.mulVecLin) = 1 := by omega
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 → ZMod p, N.mulVec v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hN (by
      ext i j
      have h2 := congrFun (h (Pi.single j 1)) i
      rwa [Matrix.mulVec_single_one, Matrix.col_apply] at h2)
  set e : Fin 2 → ZMod p := N.mulVec v with hedef
  have he : e ≠ 0 := hv
  have hNe : N.mulVec e = 0 := by
    rw [hedef, Matrix.mulVec_mulVec, ← pow_two, hN2, Matrix.zero_mulVec]
  refine ⟨e, he, hNe, fun w hw => ?_⟩
  have he_mem : e ∈ LinearMap.ker N.mulVecLin := by
    rw [LinearMap.mem_ker]; simpa [Matrix.mulVecLin_apply] using hNe
  have hspan_le : Submodule.span (ZMod p) ({e} : Set (Fin 2 → ZMod p))
      ≤ LinearMap.ker N.mulVecLin := by
    rw [Submodule.span_singleton_le_iff_mem]; exact he_mem
  have h1 : Module.finrank (ZMod p)
      ↥(Submodule.span (ZMod p) ({e} : Set (Fin 2 → ZMod p))) = 1 :=
    finrank_span_singleton he
  have hEq : Submodule.span (ZMod p) ({e} : Set (Fin 2 → ZMod p))
      = LinearMap.ker N.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [h1, hfk])
  have hw_mem : w ∈ LinearMap.ker N.mulVecLin := by
    rw [LinearMap.mem_ker]; simpa [Matrix.mulVecLin_apply] using hw
  rwa [← hEq] at hw_mem

/-! ## The group-theoretic input -/

/-- The order of `GL(2, p)`. -/
private lemma card_GL_two (p : ℕ) [Fact p.Prime] :
    Nat.card (GL (Fin 2) (ZMod p)) = p * ((p - 1) ^ 2 * (p + 1)) := by
  have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [Matrix.card_GL_field]
  rw [Fin.prod_univ_two]
  rw [ZMod.card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have h1 : ((p ^ 2 - 1 : ℕ) : ℤ) = (p : ℤ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p ^ 2)]; push_cast; ring
  have h2 : ((p ^ 2 - p : ℕ) : ℤ) = (p : ℤ) ^ 2 - p := by
    rw [Nat.cast_sub (by nlinarith : p ≤ p ^ 2)]; push_cast; ring
  have h3 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [h1, h2, h3]
  ring

/-- If `x ∈ G` has order `p` and `G ≤ GL(2, p)` has odd order divisible by `p`, then `⟨x⟩` is
normal in `G`: the Sylow `p`-subgroup of `G` is unique and equal to `⟨x⟩`. -/
private lemma conj_mem_zpowers {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (G : Subgroup (GL (Fin 2) (ZMod p))) (hp : p ∣ Nat.card G) (hodd : Odd (Nat.card G))
    (x : ↥G) (hx : orderOf x = p) :
    ∀ g : ↥G, g * x * g⁻¹ ∈ Subgroup.zpowers x := by
  have hcard : Nat.card (Sylow p ↥G) = 1 := sylow_card_eq_one hpodd G hodd hp
  haveI : Subsingleton (Sylow p ↥G) := (Nat.card_eq_one_iff_unique.mp hcard).1
  have hzx_card : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have hzx_pg : IsPGroup p (Subgroup.zpowers x) := IsPGroup.of_card (by rw [hzx_card, pow_one])
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow hzx_pg
  have hPnorm : (P : Subgroup ↥G).Normal := Sylow.normal_of_subsingleton P
  have hPcard : Nat.card (P : Subgroup ↥G) = p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
    have hdvd : Nat.card (P : Subgroup ↥G) ∣ p * ((p - 1) ^ 2 * (p + 1)) := by
      rw [← card_GL_two p]
      exact (Subgroup.card_subgroup_dvd_card (P : Subgroup ↥G)).trans
        (Subgroup.card_subgroup_dvd_card G)
    rw [hk] at hdvd
    have hp_not_dvd : ¬ p ∣ (p - 1) ^ 2 * (p + 1) := by
      have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      intro h
      rw [(Fact.out : p.Prime).dvd_mul] at h
      rcases h with h | h
      · have hp1 : p ∣ p - 1 := (Fact.out : p.Prime).dvd_of_dvd_pow h
        have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hp1
        omega
      · have hp1 : p ∣ (p + 1) - p := Nat.dvd_sub h (dvd_refl p)
        have : p ∣ 1 := by simpa using hp1
        exact (Fact.out : p.Prime).not_dvd_one this
    have hcop : Nat.Coprime (p ^ k) ((p - 1) ^ 2 * (p + 1)) :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd).pow_left k
    have hpk_dvd_p : p ^ k ∣ p := hcop.dvd_of_dvd_mul_right hdvd
    have hk_le : k ≤ 1 := by
      have hh := (Fact.out : p.Prime).pow_dvd_iff_le_factorization (k := k) (n := p) (Fact.out : p.Prime).pos.ne'
      rw [(Fact.out : p.Prime).factorization_self] at hh
      exact hh.mp hpk_dvd_p
    have hk1 : k = 1 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exfalso
        have hle : Nat.card (Subgroup.zpowers x) ≤ Nat.card (P : Subgroup ↥G) :=
          Subgroup.card_le_of_le hPle
        rw [hzx_card, hk, h, pow_zero] at hle
        have := (Fact.out : p.Prime).two_le
        omega
      · omega
    rw [hk, hk1, pow_one]
  have hPeq : Subgroup.zpowers x = (P : Subgroup ↥G) := by
    apply Subgroup.eq_of_le_of_card_ge hPle
    rw [hPcard, hzx_card]
  intro g
  have hmem : x ∈ (P : Subgroup ↥G) := hPeq.symm ▸ Subgroup.mem_zpowers x
  have hconj := hPnorm.conj_mem x hmem g
  rwa [← hPeq] at hconj

/-! ## The main theorem -/

theorem preserves_line_of_prime_dvd_card {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (G : Subgroup (GL (Fin 2) (ZMod p))) (hp : p ∣ Nat.card G) (hodd : Odd (Nat.card G)) :
    ∃ e : Fin 2 → ZMod p, e ≠ 0 ∧
      ∀ g ∈ G, (g : Matrix (Fin 2) (Fin 2) (ZMod p)).mulVec e ∈ Submodule.span (ZMod p) {e} := by
  classical
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥G) p hp
  have hnorm := conj_mem_zpowers hpodd G hp hodd x hx
  let mat : ↥G →* Matrix (Fin 2) (Fin 2) (ZMod p) :=
    (Units.coeHom (Matrix (Fin 2) (Fin 2) (ZMod p))).comp (Subgroup.subtype G)
  have hmat_inj : Function.Injective mat := by
    intro y z h
    have h1 : (y : GL (Fin 2) (ZMod p)) = (z : GL (Fin 2) (ZMod p)) := Units.ext h
    exact Subtype.ext h1
  set A : Matrix (Fin 2) (Fin 2) (ZMod p) := mat x with hAdef
  have hAp : A ^ p = 1 := by
    have h1 : x ^ p = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hx] at h
    have h2 : mat (x ^ p) = mat 1 := by rw [h1]
    rw [map_pow] at h2
    simpa [hAdef] using h2
  have hx_ne : x ≠ 1 := by
    intro h1
    have h2 : orderOf x = 1 := by rw [h1]; exact orderOf_one
    rw [hx] at h2
    exact (Fact.out : p.Prime).ne_one h2
  have hAne : A ≠ 1 := by
    intro h
    exact hx_ne (hmat_inj (by rw [← hAdef, h, map_one]))
  have hsq : (A - 1) ^ 2 = 0 := sq_sub_one_eq_zero hpodd A hAp hAne
  have hNne : A - 1 ≠ 0 := fun h => hAne (sub_eq_zero.mp h)
  obtain ⟨e, he, hNe, hker⟩ := exists_fixed_vec_of_sq_eq_zero (A - 1) hNne hsq
  refine ⟨e, he, ?_⟩
  intro g hg
  set u : ↥G := ⟨g, hg⟩ with hu
  have hmat_u : mat u = (g : Matrix (Fin 2) (Fin 2) (ZMod p)) := rfl
  have hconj := hnorm u
  have hfin : IsOfFinOrder x := isOfFinOrder_of_finite x
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff (u * x * u⁻¹) x).mp
    ((hfin.mem_powers_iff_mem_zpowers).mpr hconj)
  -- the conjugated element is a natural power of `x`
  have hBA' : mat u * mat x = mat (x ^ m) * mat u := by
    have hkey : u * x = x ^ m * u := by
      have h1 : (u * x * u⁻¹) * u = x ^ m * u := by rw [hm]
      rwa [show (u * x * u⁻¹) * u = u * x from by group] at h1
    rw [← map_mul, ← map_mul, hkey]
  rw [map_pow] at hBA'
  have hpowm : A ^ m = 1 + (m : ZMod p) • (A - 1) := by
    have h := one_add_pow_eq (A - 1) hsq m
    have hA1 : (1 + (A - 1) : Matrix (Fin 2) (Fin 2) (ZMod p)) = A := by
      rw [add_comm, sub_add_cancel]
    rwa [hA1] at h
  have hc : (m : ZMod p) ≠ 0 := by
    intro hc0
    have hxm : x ^ m = 1 := by
      apply hmat_inj
      rw [map_pow, ← hAdef, hpowm, hc0, zero_smul, add_zero, map_one]
    have hx1 : x = 1 := by
      have h1 : u * x * u⁻¹ = 1 := by rw [← hm, hxm]
      have h2 : u * x = u * 1 := by
        have h3 := congrArg (· * u) h1
        simpa [mul_assoc] using h3
      exact mul_left_cancel h2
    exact hx_ne hx1
  have hBN : mat u * (A - 1) = (m : ZMod p) • ((A - 1) * mat u) := by
    have h1 : mat u * A = A ^ m * mat u := by
      rw [← hAdef] at hBA'
      exact hBA'
    rw [hpowm, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at h1
    rw [Matrix.mul_sub, Matrix.mul_one, h1, add_sub_cancel_left]
  have key : (m : ZMod p) • (((A - 1) * mat u).mulVec e) = 0 := by
    rw [← Matrix.smul_mulVec, ← hBN, ← Matrix.mulVec_mulVec, hNe, Matrix.mulVec_zero]
  have hzero : ((A - 1) * mat u).mulVec e = 0 := (smul_eq_zero.mp key).resolve_left hc
  have hfinal : (A - 1).mulVec (mat u *ᵥ e) = 0 := by
    rw [Matrix.mulVec_mulVec]
    exact hzero
  have hthis := hker (mat u *ᵥ e) hfinal
  rwa [hmat_u] at hthis

end

end Work.GL2odd
