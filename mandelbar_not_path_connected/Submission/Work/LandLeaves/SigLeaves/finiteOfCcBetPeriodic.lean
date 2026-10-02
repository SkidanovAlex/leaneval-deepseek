import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.fract_orbit_sum_gt_one
import Submission.Work.LandLeaves.same_period_defs
import Submission.Work.LandLeaves.finite_of_fixed_fract
import Submission.Work.LandLeaves.iterate_fixes_all_of_ccBet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
A copy of `Work.LandLeaves.finite_of_ccBet_periodic_point` in its own namespace.

The copy is needed because the original file defines `Work.LandLeaves.fract_sub_fract_of_le`,
which `Work.LandLeaves.ccBet_v2_defs` defines as well; importing both files in one module is
rejected by Lean ("environment already contains ...").  This is the same statement, proved by the
same argument, in the namespace `Work.LandLeaves.SigLeaves`, so that it can be used together with
the angle--side (pairSide) vocabulary.
-/

namespace Work.LandLeaves.SigLeaves

open Classical

noncomputable section

/-! ## Elementary `Int.fract` manipulations -/

theorem fract_mul_fract_nat (n : ℕ) (x : ℝ) :
    Int.fract ((n : ℝ) * Int.fract x) = Int.fract ((n : ℝ) * x) := by
  rw [Int.fract_eq_fract]
  refine ⟨-(n * ⌊x⌋), ?_⟩
  have h : Int.fract x = x - ⌊x⌋ := by have := Int.self_sub_fract x; linarith
  rw [h]; push_cast; ring

theorem fract_iterate_mul_eq (d : ℕ) {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    (fun z : ℝ => Int.fract ((d : ℝ) * z))^[n] x = Int.fract (((d : ℝ)^n) * x) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Function.iterate_succ_apply', ih,
        fract_mul_fract_nat d, pow_succ']
      ring_nf

theorem fract_sub_fract_of_le {a b : ℝ} (h : Int.fract b ≤ Int.fract a) :
    Int.fract a - Int.fract b = Int.fract (a - b) := by
  have key : Int.fract (Int.fract a - Int.fract b) = Int.fract a - Int.fract b := by
    refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
    · linarith
    · linarith [Int.fract_lt_one a, Int.fract_nonneg b]
  rw [← fract_sub_fract a b]
  exact key.symm

/-! ## The core: one periodic point forces every point to be periodic -/

theorem all_periodic_of_one_periodic {d : ℕ} (hd : 2 ≤ d) {K : Set ℝ}
    (hsub : ∀ x ∈ K, 0 ≤ x ∧ x < 1)
    (hmap : ∀ x ∈ K, Int.fract ((d : ℝ) * x) ∈ K)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, Int.fract ((d : ℝ) * x) = Int.fract ((d : ℝ) * y) → x = y)
    (hord : ∀ a ∈ K, ∀ b ∈ K, ∀ x ∈ K, ccBet a b x →
      ccBet (Int.fract ((d : ℝ) * a)) (Int.fract ((d : ℝ) * b)) (Int.fract ((d : ℝ) * x)))
    {q : ℕ} (hq : 0 < q) {p : ℝ} (hp : p ∈ K)
    (hper : (fun x : ℝ => Int.fract ((d : ℝ) * x))^[q] p = p) :
    ∀ a ∈ K, ∃ m : ℕ, 0 < m ∧ (fun x : ℝ => Int.fract ((d : ℝ) * x))^[m] a = a := by
  intro a ha
  by_cases hap : a = p
  · exact ⟨q, hq, by rw [hap]; exact hper⟩
  by_contra hcon
  push_neg at hcon
  let σ : ℝ → ℝ := fun x : ℝ => Int.fract ((d : ℝ) * x)
  have hMcast : ((d ^ q : ℕ) : ℝ) = (d : ℝ)^q := by push_cast; ring
  have hτ : ∀ z : ℝ, σ^[q] z = Int.fract (((d ^ q : ℕ) : ℝ) * z) := by
    intro z
    have h1 : σ^[q] z = (fun x : ℝ => Int.fract ((d : ℝ) * x))^[q] z := rfl
    rw [h1, fract_iterate_mul_eq d hq z, hMcast]
  have hexp : ∀ u v : ℝ, Int.fract (σ^[q] u - σ^[q] v)
      = Int.fract (((d ^ q : ℕ) : ℝ) * (u - v)) := by
    intro u v
    rw [hτ, hτ, fract_sub_fract]
    congr 1
    ring
  have hmem : ∀ n (z : ℝ), z ∈ K → σ^[n] z ∈ K := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih => intro z hz; rw [Function.iterate_succ_apply']; exact hmap _ (ih z hz)
  have hinj' : ∀ n (x y : ℝ), x ∈ K → y ∈ K → σ^[n] x = σ^[n] y → x = y := by
    intro n
    induction n with
    | zero => intro x y hx hy h; simpa using h
    | succ n ih =>
        intro x y hx hy h
        simp only [Function.iterate_succ_apply'] at h
        exact ih x y hx hy (hinj _ (hmem n x hx) _ (hmem n y hy) h)
  have hord' : ∀ n (x y z : ℝ), x ∈ K → y ∈ K → z ∈ K → ccBet x y z →
      ccBet (σ^[n] x) (σ^[n] y) (σ^[n] z) := by
    intro n
    induction n with
    | zero => intro x y z _ _ _ h; simpa using h
    | succ n ih =>
        intro x y z hx hy hz h
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply']
        exact hord _ (hmem n x hx) _ (hmem n y hy) _ (hmem n z hz) (ih x y z hx hy hz h)
  have hτp : σ^[q] p = p := hper
  have hτmem : ∀ z ∈ K, σ^[q] z ∈ K := fun z hz => hmem q z hz
  have hτinj : ∀ x ∈ K, ∀ y ∈ K, σ^[q] x = σ^[q] y → x = y :=
    fun x hx y hy h => hinj' q x y hx hy h
  have hτmem' : ∀ n (z : ℝ), z ∈ K → (σ^[q])^[n] z ∈ K := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih => intro z hz; rw [Function.iterate_succ_apply']; exact hτmem _ (ih z hz)
  have hτinj' : ∀ n (x y : ℝ), x ∈ K → y ∈ K → (σ^[q])^[n] x = (σ^[q])^[n] y → x = y := by
    intro n
    induction n with
    | zero => intro x y hx hy h; simpa using h
    | succ n ih =>
        intro x y hx hy h
        simp only [Function.iterate_succ_apply'] at h
        exact ih x y hx hy (hτinj _ (hτmem' n x hx) _ (hτmem' n y hy) h)
  have hτfix : ∀ n, (σ^[q])^[n] p = p := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]; exact hτp
  have hbase : ∀ n, (σ^[q])^[n] a ∈ K := fun n => hτmem' n a ha
  have hne_p : ∀ n, (σ^[q])^[n] a ≠ p := by
    intro n h
    have h2 : (σ^[q])^[n] a = (σ^[q])^[n] p := by rw [h, hτfix n]
    exact hap (hτinj' n a p ha hp h2)
  have hρinj : ∀ x ∈ K, ∀ y ∈ K, Int.fract (x - p) = Int.fract (y - p) → x = y := by
    intro x hx y hy h
    obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h
    have hxy : x - y = (z : ℝ) := by linarith
    have h1 : (z : ℝ) < 1 := by linarith [(hsub x hx).2, (hsub y hy).1]
    have h2 : (-1 : ℝ) < (z : ℝ) := by linarith [(hsub x hx).1, (hsub y hy).2]
    have h3 : z < (1 : ℤ) := by exact_mod_cast h1
    have h4 : (-1 : ℤ) < z := by exact_mod_cast h2
    have h5 : z = 0 := by omega
    rw [h5] at hxy; push_cast at hxy; linarith
  let u : ℕ → ℝ := fun n => Int.fract ((σ^[q])^[n] a - p)
  have hu01 : ∀ n, 0 ≤ u n ∧ u n < 1 := fun n => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hu_ne0 : ∀ n, u n ≠ 0 := by
    intro n h
    have hm := hbase n
    have hz : ∃ z : ℤ, ((σ^[q])^[n] a - p) = (z : ℝ) := by
      obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h
      exact ⟨z, hz.symm⟩
    obtain ⟨z, hz⟩ := hz
    have h1 : (z : ℝ) < 1 := by linarith [(hsub _ hm).2, (hsub p hp).1]
    have h2 : (-1 : ℝ) < (z : ℝ) := by linarith [(hsub _ hm).1, (hsub p hp).2]
    have h3 : z < (1 : ℤ) := by exact_mod_cast h1
    have h4 : (-1 : ℤ) < z := by exact_mod_cast h2
    have h5 : z = 0 := by omega
    have h6 : (z : ℝ) = 0 := by rw [h5]; norm_num
    exact hne_p n (by linarith [hz, h6])
  have hcc_of_lt : ∀ m n : ℕ, u m < u n → ccBet p ((σ^[q])^[n] a) ((σ^[q])^[m] a) := by
    intro m n h
    exact ⟨lt_of_le_of_ne (hu01 m).1 (Ne.symm (hu_ne0 m)), h⟩
  have hshift : ∀ m n : ℕ, u m < u n → u (m+1) < u (n+1) := by
    intro m n h
    have h1 := hord' q p ((σ^[q])^[n] a) ((σ^[q])^[m] a) hp (hbase n) (hbase m)
      (hcc_of_lt m n h)
    have hA : σ^[q] ((σ^[q])^[n] a) = (σ^[q])^[n+1] a :=
      (Function.iterate_succ_apply' (σ^[q]) n a).symm
    have hB : σ^[q] ((σ^[q])^[m] a) = (σ^[q])^[m+1] a :=
      (Function.iterate_succ_apply' (σ^[q]) m a).symm
    rw [hτp, hA, hB] at h1
    exact h1.2
  have hpow_ne : ∀ m n : ℕ, m < n → (σ^[q])^[m] a ≠ (σ^[q])^[n] a := by
    intro m n hmn h
    have h1 : (σ^[q])^[m] ((σ^[q])^[n-m] a) = (σ^[q])^[m] a := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hmn.le]
      exact h.symm
    have h2 : (σ^[q])^[n-m] a = a := hτinj' m _ _ (hτmem' _ a ha) ha h1
    have h3 : σ^[q*(n-m)] a = a := by
      rw [Function.iterate_mul]
      exact h2
    exact hcon (q*(n-m)) (Nat.mul_pos hq (Nat.sub_pos_of_lt hmn)) h3
  have hdist : ∀ m n : ℕ, m ≠ n → u m ≠ u n := by
    intro m n hmn h
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · exact hpow_ne m n hlt (hρinj _ (hbase m) _ (hbase n) h)
    · exact hpow_ne n m hgt (hρinj _ (hbase n) _ (hbase m) h.symm)
  have hmono : (∀ n, u n < u (n+1)) ∨ (∀ n, u (n+1) < u n) := by
    rcases lt_or_gt_of_ne (hdist 0 1 (by norm_num)) with h0 | h0
    · left
      intro n
      induction n with
      | zero => exact h0
      | succ n ih => exact hshift n (n+1) ih
    · right
      intro n
      induction n with
      | zero => exact h0
      | succ n ih => exact hshift (n+1) n ih
  have hM1 : (1 : ℝ) < ((d ^ q : ℕ) : ℝ) := by
    have h2 : 2 ≤ d ^ q := by
      calc 2 ≤ d := hd
        _ = d ^ 1 := (pow_one d).symm
        _ ≤ d ^ q := Nat.pow_le_pow_right (by omega) hq
    have h3 : (2 : ℝ) ≤ ((d ^ q : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  rcases hmono with hup | hdown
  · let lam : ℕ → ℝ := fun n => u (n+1) - u n
    have hlam_eq : ∀ n, lam n = Int.fract ((σ^[q])^[n+1] a - (σ^[q])^[n] a) := by
      intro n
      show u (n+1) - u n = Int.fract ((σ^[q])^[n+1] a - (σ^[q])^[n] a)
      have h1 : u (n+1) = Int.fract ((σ^[q])^[n+1] a - p) := rfl
      have h2 : u n = Int.fract ((σ^[q])^[n] a - p) := rfl
      rw [h1, h2, fract_sub_fract_of_le (le_of_lt (hup n))]
      congr 1
      ring
    have hlam_pos : ∀ n, 0 < lam n := by
      intro n; show 0 < u (n+1) - u n; linarith [hup n]
    have hlam_step : ∀ n, lam (n+1) = Int.fract (((d ^ q : ℕ) : ℝ) * lam n) := by
      intro n
      have e1 : (σ^[q])^[n+1+1] a = σ^[q] ((σ^[q])^[n+1] a) :=
        Function.iterate_succ_apply' _ _ _
      have e2 : (σ^[q])^[n+1] a = σ^[q] ((σ^[q])^[n] a) :=
        Function.iterate_succ_apply' _ _ _
      have s1 : (σ^[q])^[n+1+1] a - (σ^[q])^[n+1] a
          = σ^[q] ((σ^[q])^[n+1] a) - (σ^[q])^[n+1] a := by rw [e1]
      have s2 : σ^[q] ((σ^[q])^[n+1] a) - (σ^[q])^[n+1] a
          = σ^[q] ((σ^[q])^[n+1] a) - σ^[q] ((σ^[q])^[n] a) :=
        congrArg (fun t => σ^[q] ((σ^[q])^[n+1] a) - t) e2
      have h1 : lam (n+1)
          = Int.fract (σ^[q] ((σ^[q])^[n+1] a) - σ^[q] ((σ^[q])^[n] a)) := by
        rw [hlam_eq (n+1), s1, s2]
      rw [h1, hexp, hlam_eq n, fract_mul_fract_nat (d^q)]
    have hsum_le : ∀ N, ∑ n ∈ Finset.range N, lam n ≤ 1 := by
      intro N
      have htel : ∑ n ∈ Finset.range N, lam n = u N - u 0 :=
        show ∑ n ∈ Finset.range N, (u (n+1) - u n) = u N - u 0 from Finset.sum_range_sub u N
      rw [htel]
      linarith [(hu01 N).2, (hu01 0).1]
    obtain ⟨N, hN⟩ := fract_orbit_sum_gt_one hM1 hlam_step hlam_pos
    linarith [hsum_le N]
  · let lam : ℕ → ℝ := fun n => u n - u (n+1)
    have hlam_eq : ∀ n, lam n = Int.fract ((σ^[q])^[n] a - (σ^[q])^[n+1] a) := by
      intro n
      show u n - u (n+1) = Int.fract ((σ^[q])^[n] a - (σ^[q])^[n+1] a)
      have h1 : u n = Int.fract ((σ^[q])^[n] a - p) := rfl
      have h2 : u (n+1) = Int.fract ((σ^[q])^[n+1] a - p) := rfl
      rw [h1, h2, fract_sub_fract_of_le (le_of_lt (hdown n))]
      congr 1
      ring
    have hlam_pos : ∀ n, 0 < lam n := by
      intro n; show 0 < u n - u (n+1); linarith [hdown n]
    have hlam_step : ∀ n, lam (n+1) = Int.fract (((d ^ q : ℕ) : ℝ) * lam n) := by
      intro n
      have e1 : (σ^[q])^[n+1+1] a = σ^[q] ((σ^[q])^[n+1] a) :=
        Function.iterate_succ_apply' _ _ _
      have e2 : (σ^[q])^[n+1] a = σ^[q] ((σ^[q])^[n] a) :=
        Function.iterate_succ_apply' _ _ _
      have t1 : (σ^[q])^[n+1] a - (σ^[q])^[n+1+1] a
          = σ^[q] ((σ^[q])^[n] a) - (σ^[q])^[n+1+1] a := by rw [e2]
      have t2 : σ^[q] ((σ^[q])^[n] a) - (σ^[q])^[n+1+1] a
          = σ^[q] ((σ^[q])^[n] a) - σ^[q] ((σ^[q])^[n+1] a) :=
        congrArg (fun t => σ^[q] ((σ^[q])^[n] a) - t) e1
      have h1 : lam (n+1)
          = Int.fract (σ^[q] ((σ^[q])^[n] a) - σ^[q] ((σ^[q])^[n+1] a)) := by
        rw [hlam_eq (n+1), t1, t2]
      rw [h1, hexp, hlam_eq n, fract_mul_fract_nat (d^q)]
    have hsum_le : ∀ N, ∑ n ∈ Finset.range N, lam n ≤ 1 := by
      intro N
      have htel : ∑ n ∈ Finset.range N, lam n = u 0 - u N :=
        show ∑ n ∈ Finset.range N, (u n - u (n+1)) = u 0 - u N from Finset.sum_range_sub' u N
      rw [htel]
      linarith [(hu01 N).1, (hu01 0).2]
    obtain ⟨N, hN⟩ := fract_orbit_sum_gt_one hM1 hlam_step hlam_pos
    linarith [hsum_le N]

/-! ## The target -/

/-- **A `σ`-invariant set containing one periodic point is finite.**

Let `d ≥ 2` and let `K ⊆ [0,1)` be closed under the angle map `σ x = Int.fract (d * x)`, with
`σ` a bijection of `K` onto itself preserving cyclic betweenness `ccBet` on `K`.  If `K`
contains a point `p` which is periodic of period `q ≥ 1` for `σ`, then `K` is finite. -/
theorem finite_of_ccBet_periodic_point {d : ℕ} (hd : 2 ≤ d) {K : Set ℝ}
    (hsub : ∀ x ∈ K, 0 ≤ x ∧ x < 1)
    (hmap : ∀ x ∈ K, Int.fract ((d : ℝ) * x) ∈ K)
    (hsurj : ∀ y ∈ K, ∃ x ∈ K, Int.fract ((d : ℝ) * x) = y)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, Int.fract ((d : ℝ) * x) = Int.fract ((d : ℝ) * y) → x = y)
    (hord : ∀ a ∈ K, ∀ b ∈ K, ∀ x ∈ K, Work.LandLeaves.ccBet a b x →
      Work.LandLeaves.ccBet (Int.fract ((d : ℝ) * a)) (Int.fract ((d : ℝ) * b))
        (Int.fract ((d : ℝ) * x)))
    {q : ℕ} (hq : 0 < q) {p : ℝ} (hp : p ∈ K)
    (hper : (fun x : ℝ => Int.fract ((d : ℝ) * x))^[q] p = p) :
    K.Finite := by
  -- (1) The periodic point `p` forces every point of `K` to be `σ`-periodic.
  have hperall : ∀ a ∈ K, ∃ m : ℕ, 0 < m ∧
      (fun x : ℝ => Int.fract ((d : ℝ) * x))^[m] a = a :=
    all_periodic_of_one_periodic hd hsub hmap hinj hord hq hp hper
  -- (2) Hence `σ^[q]`, which fixes `p`, fixes every point of `K`.
  have hfix : ∀ y ∈ K, (fun z : ℝ => Int.fract ((d : ℝ) * z))^[q] y = y :=
    iterate_fixes_all_of_ccBet hd hsub hmap hinj hord hperall hq hp hper
  -- (3) So `K` is contained in the set of fixed points of `x ↦ Int.fract (d^q * x)`.
  have hnat : ((d : ℝ)^q) = ((d ^ q : ℕ) : ℝ) := by push_cast; ring
  have hM2 : 2 ≤ d ^ q := by
    calc 2 ≤ d := hd
      _ = d ^ 1 := (pow_one d).symm
      _ ≤ d ^ q := Nat.pow_le_pow_right (by omega) hq
  refine (finite_of_fixed_fract hM2).subset ?_
  intro y hy
  obtain ⟨hy0, hy1⟩ := hsub y hy
  refine ⟨⟨hy0, hy1⟩, ?_⟩
  have h := hfix y hy
  rwa [fract_iterate_mul_eq d hq y, hnat] at h

end

end Work.LandLeaves.SigLeaves
