import Mathlib.Data.Nat.GCD.Prime
import Submission.Commons.NumberTheory.DuffinSchaeffer.reduced_pair_count_prime_pow
import Submission.Commons.Data.Nat.pair_count_freshM
import Submission.Commons.Data.Nat.mul_div_gcd_eq_lcm
import Submission.Commons.Data.Nat.factorization_prod_prime_pow_apply

open scoped BigOperators

namespace Commons.NumberTheory.DuffinSchaeffer


/-- The pair-fiber count: number of reduced pairs (a mod m, b mod n) with
a·X ≡ b·Y + e (mod L). -/
def pairFiber (m n X Y L e : ℕ) : ℕ :=
  (((Finset.product ((Finset.range m).filter (fun a : ℕ => a.gcd m = 1))
      ((Finset.range n).filter (fun b : ℕ => b.gcd n = 1))).filter
    (fun ab : ℕ × ℕ => ((ab.1 * X) % L = ((ab.2 * Y + e) % L)))).card)

/-- The underlying filtered set of pairs. -/
def FS (m n X Y L e : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.product ((Finset.range m).filter (fun a : ℕ => a.gcd m = 1))
      ((Finset.range n).filter (fun b : ℕ => b.gcd n = 1))).filter
    (fun ab : ℕ × ℕ => ((ab.1 * X) % L = ((ab.2 * Y + e) % L))))

lemma FS_card (m n X Y L e : ℕ) : (FS m n X Y L e).card = pairFiber m n X Y L e := rfl

/-- membership in FS -/
lemma mem_FS {m n X Y L e : ℕ} {a b : ℕ} :
    (a, b) ∈ FS m n X Y L e ↔
      a < m ∧ a.gcd m = 1 ∧ b < n ∧ b.gcd n = 1 ∧
        ((a * X) % L = ((b * Y + e) % L)) := by
  simp [FS, Finset.mem_product, Finset.mem_filter, and_assoc]

lemma mem_FS_coprime {m n X Y L e : ℕ} {a b : ℕ} (h : (a, b) ∈ FS m n X Y L e) :
    a.Coprime m ∧ b.Coprime n := by
  rcases mem_FS.mp h with ⟨_, hgm, _, hgn, _⟩
  exact ⟨Nat.coprime_iff_gcd_eq_one.mpr hgm, Nat.coprime_iff_gcd_eq_one.mpr hgn⟩

lemma mem_FS_lt {m n X Y L e : ℕ} {a b : ℕ} (h : (a, b) ∈ FS m n X Y L e) : a < m ∧ b < n := by
  rcases mem_FS.mp h with ⟨ham, _, hbn, _, _⟩
  exact ⟨ham, hbn⟩

lemma mem_FS_congr {m n X Y L e : ℕ} {a b : ℕ} (h : (a, b) ∈ FS m n X Y L e) :
    ((a * X) % L = ((b * Y + e) % L)) := (mem_FS.mp h).2.2.2.2

-- gcd helpers
lemma gcd_mod_left (a b : ℕ) : (a % b).gcd b = a.gcd b := by
  calc
    (a % b).gcd b = b.gcd (a % b) := Nat.gcd_comm (a % b) b
    _ = b.gcd a := by
      rw [Nat.gcd_rec b a]
      rw [Nat.gcd_comm]
    _ = a.gcd b := Nat.gcd_comm b a

lemma gcd_mod_eq_one_of_gcd {a m : ℕ} (h : a.gcd m = 1) : (a % m).gcd m = 1 := by
  rw [gcd_mod_left]
  exact h

lemma gcd_mul_eq_one_iff {a m n : ℕ} (hmn : m.Coprime n) :
    a.gcd (m * n) = 1 ↔ a.gcd m = 1 ∧ a.gcd n = 1 := by
  rw [← Nat.coprime_iff_gcd_eq_one, ← Nat.coprime_iff_gcd_eq_one, ← Nat.coprime_iff_gcd_eq_one]
  exact Nat.coprime_mul_iff_right (k := a)

lemma mul_mod_eq_zero_of_mod_eq_zero {k c L : ℕ} (h : c % L = 0) : (k * c) % L = 0 := by
  rw [Nat.mul_mod, h]
  simp

lemma mul_remainder_eq_of_dvd_mul_left {a m X L : ℕ} (h : L ∣ m * X) :
    (a * X) % L = ((a % m) * X) % L := by
  have hbb : a * X = (a % m + m * (a / m)) * X := by
    rw [Nat.mod_add_div]
  have hz : (m * X) % L = 0 := Nat.mod_eq_zero_of_dvd h
  have hz2 : ((a / m) * (m * X)) % L = 0 := mul_mod_eq_zero_of_mod_eq_zero hz
  calc
    (a * X) % L = ((a % m + m * (a / m)) * X) % L := by rw [hbb]
    _ = ((a % m) * X + (a / m) * (m * X)) % L := by
      congr 1
      ring
    _ = ((((a % m) * X) % L) + (((a / m) * (m * X)) % L)) % L := by rw [Nat.add_mod]
    _ = (((a % m) * X) % L) := by rw [hz2, add_zero, Nat.mod_mod]

lemma add_mul_remainder_eq_of_dvd_mul_left {b n Y e L : ℕ} (h : L ∣ n * Y) :
    (b * Y + e) % L = ((b % n) * Y + e) % L := by
  have hbb : b * Y + e = (b % n + n * (b / n)) * Y + e := by
    rw [Nat.mod_add_div]
  have hz : (n * Y) % L = 0 := Nat.mod_eq_zero_of_dvd h
  have hz2 : ((b / n) * (n * Y)) % L = 0 := mul_mod_eq_zero_of_mod_eq_zero hz
  calc
    (b * Y + e) % L = ((b % n + n * (b / n)) * Y + e) % L := by rw [hbb]
    _ = ((b % n) * Y + (b / n) * (n * Y) + e) % L := by
      congr 1
      ring
    _ = ((((b % n) * Y + (b / n) * (n * Y)) % L) + e % L) % L := by rw [Nat.add_mod]
    _ = (((((b % n) * Y) % L + ((b / n) * (n * Y)) % L) % L) + e % L) % L := by
      congr 2
      rw [Nat.add_mod]
    _ = ((((b % n) * Y) % L + e % L) % L) := by
      rw [hz2]
      simp [Nat.add_mod]
    _ = ((b % n) * Y + e) % L := by rw [← Nat.add_mod]

lemma mod_mod_of_dvd_eq {a b c : ℕ} (h : c ∣ b) : a % b % c = a % c := Nat.mod_mod_of_dvd a h

lemma remainder_eq_of_lt {a L : ℕ} (h : a < L) : a % L = a := Nat.mod_eq_of_lt h

-- ============ CRT split helpers ============

/-- from gcd(a, m*n)=1 and m.Coprime n we get gcd(a,m)=1 and gcd(a,n)=1 -/
lemma gcd_left_of_gcd_mul {a m n : ℕ} (hmn : m.Coprime n) (h : a.gcd (m * n) = 1) :
    a.gcd m = 1 := by
  have hboth : a.gcd m = 1 ∧ a.gcd n = 1 := (gcd_mul_eq_one_iff hmn).mp h
  exact hboth.1

lemma gcd_right_of_gcd_mul {a m n : ℕ} (hmn : m.Coprime n) (h : a.gcd (m * n) = 1) :
    a.gcd n = 1 := by
  have hboth : a.gcd m = 1 ∧ a.gcd n = 1 := (gcd_mul_eq_one_iff hmn).mp h
  exact hboth.2

/-- aX mod L depends only on a mod m when L | m*X -/
lemma mul_remainder_congr_of_mod {a a' m X L : ℕ} (hm : a ≡ a' [MOD m]) (h : L ∣ m * X) :
    (a * X) % L = (a' * X) % L := by
  have hmm : a % m = a' % m := hm
  calc
    (a * X) % L = ((a % m) * X) % L := mul_remainder_eq_of_dvd_mul_left h
    _ = ((a' % m) * X) % L := by rw [hmm]
    _ = (a' * X) % L := (mul_remainder_eq_of_dvd_mul_left h).symm

lemma add_mul_remainder_congr_of_mod {b b' n Y e L : ℕ} (hn : b ≡ b' [MOD n]) (h : L ∣ n * Y) :
    (b * Y + e) % L = (b' * Y + e) % L := by
  have hnn : b % n = b' % n := hn
  calc
    (b * Y + e) % L = ((b % n) * Y + e) % L := add_mul_remainder_eq_of_dvd_mul_left h
    _ = ((b' % n) * Y + e) % L := by rw [hnn]
    _ = (b' * Y + e) % L := (add_mul_remainder_eq_of_dvd_mul_left h).symm

-- u%L0 = v%L0 from u%(L0*L1) = v%(L0*L1)
lemma remainder_eq_of_mul_mod {u v L₀ L₁ : ℕ} (h : u % (L₀ * L₁) = v % (L₀ * L₁)) :
    u % L₀ = v % L₀ := by
  have hmod : u ≡ v [MOD L₀ * L₁] := h
  have h0 : u ≡ v [MOD L₀] := Nat.ModEq.of_dvd (dvd_mul_right L₀ L₁) hmod
  exact h0

lemma congr_eq_of_mul_modEq {u v L₀ L₁ : ℕ} (h0 : u % L₀ = v % L₀) (h1 : u % L₁ = v % L₁)
    (hcop : L₀.Coprime L₁) : u % (L₀ * L₁) = v % (L₀ * L₁) := by
  have h0' : u ≡ v [MOD L₀] := h0
  have h1' : u ≡ v [MOD L₁] := h1
  have h' : u ≡ v [MOD L₀ * L₁] := (Nat.modEq_and_modEq_iff_modEq_mul (m := L₀) (n := L₁) hcop).mp ⟨h0', h1'⟩
  exact h'

/-- (a%m)*X mod L = a*X mod L -/
lemma mul_remainder_eq_of_dvd_mul_left' {a m X L : ℕ} (h : L ∣ m * X) :
    ((a % m) * X) % L = (a * X) % L := (mul_remainder_eq_of_dvd_mul_left h).symm

/-- ((b%n)*Y + e) mod L = (b*Y+e) mod L -/
lemma add_mul_remainder_eq_of_dvd_mul_left' {b n Y e L : ℕ} (h : L ∣ n * Y) :
    ((b % n) * Y + e) % L = (b * Y + e) % L := (add_mul_remainder_eq_of_dvd_mul_left h).symm

/-- u%L1 = v%L1 from u%(L0*L1) = v%(L0*L1) -/
lemma remainder_eq_of_mul_mod_right {u v L₀ L₁ : ℕ} (h : u % (L₀ * L₁) = v % (L₀ * L₁)) :
    u % L₁ = v % L₁ := by
  have h' : u % (L₁ * L₀) = v % (L₁ * L₀) := by
    simpa [mul_comm] using h
  exact remainder_eq_of_mul_mod (L₀ := L₁) (L₁ := L₀) h'

-- main split lemma
theorem pairFiber_mul (m₀ m₁ n₀ n₁ X Y L₀ L₁ e : ℕ)
    (hm01 : m₀.Coprime m₁) (hn01 : n₀.Coprime n₁) (hL01 : L₀.Coprime L₁)
    (h0m : L₀ ∣ m₀ * X) (h0n : L₀ ∣ n₀ * Y) (h1m : L₁ ∣ m₁ * X) (h1n : L₁ ∣ n₁ * Y)
    (hm0 : 0 < m₀) (hm1 : 0 < m₁) (hn0 : 0 < n₀) (hn1 : 0 < n₁)
    (hL0 : 0 < L₀) (hL1 : 0 < L₁) :
    pairFiber (m₀ * m₁) (n₀ * n₁) X Y (L₀ * L₁) e =
      pairFiber m₀ n₀ X Y L₀ e * pairFiber m₁ n₁ X Y L₁ e := by
  classical
  let s : Finset (ℕ × ℕ) := FS (m₀ * m₁) (n₀ * n₁) X Y (L₀ * L₁) e
  let s₀ : Finset (ℕ × ℕ) := FS m₀ n₀ X Y L₀ e
  let s₁ : Finset (ℕ × ℕ) := FS m₁ n₁ X Y L₁ e
  have hcopm' : m₁.Coprime m₀ := Nat.coprime_comm.mpr hm01
  have hcopn' : n₁.Coprime n₀ := Nat.coprime_comm.mpr hn01
  have hcopL' : L₁.Coprime L₀ := Nat.coprime_comm.mpr hL01
  have hcard : s.card = (s₀ ×ˢ s₁).card := by
    refine Finset.card_bij
      (fun ab _ => (((ab.1 % m₀, ab.2 % n₀), (ab.1 % m₁, ab.2 % n₁)))) ?hi ?hinj ?hsurj
    · intro ab hab
      apply Finset.mem_product.mpr
      constructor
      · rw [mem_FS]
        rcases mem_FS.mp hab with ⟨ham, hgm, hbn, hgn, hcong⟩
        constructor
        · exact Nat.mod_lt ab.1 (Nat.pos_of_ne_zero (ne_of_gt hm0))
        constructor
        · exact gcd_mod_eq_one_of_gcd (gcd_left_of_gcd_mul hm01 hgm)
        constructor
        · exact Nat.mod_lt ab.2 (Nat.pos_of_ne_zero (ne_of_gt hn0))
        constructor
        · exact gcd_mod_eq_one_of_gcd (gcd_left_of_gcd_mul hn01 hgn)
        · have hcong0 : (ab.1 * X) % L₀ = (ab.2 * Y + e) % L₀ :=
            remainder_eq_of_mul_mod (u := ab.1 * X) (v := ab.2 * Y + e) (L₀ := L₀) (L₁ := L₁) hcong
          calc
            ((ab.1 % m₀) * X) % L₀ = (ab.1 * X) % L₀ := mul_remainder_eq_of_dvd_mul_left' h0m
            _ = (ab.2 * Y + e) % L₀ := hcong0
            _ = ((ab.2 % n₀) * Y + e) % L₀ := add_mul_remainder_eq_of_dvd_mul_left h0n
      · rw [mem_FS]
        rcases mem_FS.mp hab with ⟨ham, hgm, hbn, hgn, hcong⟩
        constructor
        · exact Nat.mod_lt ab.1 (Nat.pos_of_ne_zero (ne_of_gt hm1))
        constructor
        · exact gcd_mod_eq_one_of_gcd (gcd_right_of_gcd_mul hm01 hgm)
        constructor
        · exact Nat.mod_lt ab.2 (Nat.pos_of_ne_zero (ne_of_gt hn1))
        constructor
        · exact gcd_mod_eq_one_of_gcd (gcd_right_of_gcd_mul hn01 hgn)
        · have hcong1 : (ab.1 * X) % L₁ = (ab.2 * Y + e) % L₁ :=
            remainder_eq_of_mul_mod_right (u := ab.1 * X) (v := ab.2 * Y + e) (L₀ := L₀) (L₁ := L₁) hcong
          calc
            ((ab.1 % m₁) * X) % L₁ = (ab.1 * X) % L₁ := mul_remainder_eq_of_dvd_mul_left' h1m
            _ = (ab.2 * Y + e) % L₁ := hcong1
            _ = ((ab.2 % n₁) * Y + e) % L₁ := add_mul_remainder_eq_of_dvd_mul_left h1n
    · intro ab hab cd hcd hpr
      rcases mem_FS.mp hab with ⟨ham, hgm, hbn, hgn, hcong⟩
      rcases mem_FS.mp hcd with ⟨hcm, hgcm, hdn, hgdn, hcong'⟩
      have hf1 : ab.1 % m₀ = cd.1 % m₀ := by simpa using congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.1.1) hpr
      have hf2 : ab.1 % m₁ = cd.1 % m₁ := by simpa using congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.2.1) hpr
      have hmod0 : ab.1 ≡ cd.1 [MOD m₀] := hf1
      have hmod1 : ab.1 ≡ cd.1 [MOD m₁] := hf2
      have hmod : ab.1 ≡ cd.1 [MOD m₀ * m₁] :=
        (Nat.modEq_and_modEq_iff_modEq_mul (m := m₀) (n := m₁) hm01).mp ⟨hmod0, hmod1⟩
      have ha : ab.1 = cd.1 := hmod.eq_of_lt_of_lt ham hcm
      have hg1 : ab.2 % n₀ = cd.2 % n₀ := by simpa using congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.1.2) hpr
      have hg2 : ab.2 % n₁ = cd.2 % n₁ := by simpa using congrArg (fun z : (ℕ × ℕ) × (ℕ × ℕ) => z.2.2) hpr
      have hmodn0 : ab.2 ≡ cd.2 [MOD n₀] := hg1
      have hmodn1 : ab.2 ≡ cd.2 [MOD n₁] := hg2
      have hmodn : ab.2 ≡ cd.2 [MOD n₀ * n₁] :=
        (Nat.modEq_and_modEq_iff_modEq_mul (m := n₀) (n := n₁) hn01).mp ⟨hmodn0, hmodn1⟩
      have hb : ab.2 = cd.2 := hmodn.eq_of_lt_of_lt hbn hdn
      ext <;> assumption
    · intro x hx
      rcases Finset.mem_product.mp hx with ⟨hx₀, hx₁⟩
      let a₀ : ℕ := x.1.1
      let b₀ : ℕ := x.1.2
      let a₁ : ℕ := x.2.1
      let b₁ : ℕ := x.2.2
      have hx₀m := mem_FS.mp hx₀
      have hx₁m := mem_FS.mp hx₁
      have ha₀ : a₀ < m₀ := by simpa [a₀] using hx₀m.1
      have hb₀ : b₀ < n₀ := by simpa [b₀] using hx₀m.2.2.1
      have ha₁ : a₁ < m₁ := by simpa [a₁] using hx₁m.1
      have hb₁ : b₁ < n₁ := by simpa [b₁] using hx₁m.2.2.1
      have hgcd₀ : a₀.gcd m₀ = 1 := by simpa [a₀] using hx₀m.2.1
      have hgcdb₀ : b₀.gcd n₀ = 1 := by simpa [b₀] using hx₀m.2.2.2.1
      have hgcd₁ : a₁.gcd m₁ = 1 := by simpa [a₁] using hx₁m.2.1
      have hgcdb₁ : b₁.gcd n₁ = 1 := by simpa [b₁] using hx₁m.2.2.2.1
      have hcong₀ : (a₀ * X) % L₀ = (b₀ * Y + e) % L₀ := by simpa [a₀, b₀] using hx₀m.2.2.2.2
      have hcong₁ : (a₁ * X) % L₁ = (b₁ * Y + e) % L₁ := by simpa [a₁, b₁] using hx₁m.2.2.2.2
      let ka : ℕ := (Nat.chineseRemainder hcopm' a₁ a₀).1
      let kb : ℕ := (Nat.chineseRemainder hcopn' b₁ b₀).1
      have hka1 : ka ≡ a₁ [MOD m₁] := by simpa [ka] using (Nat.chineseRemainder hcopm' a₁ a₀).2.1
      have hka0 : ka ≡ a₀ [MOD m₀] := by simpa [ka] using (Nat.chineseRemainder hcopm' a₁ a₀).2.2
      have hkb1 : kb ≡ b₁ [MOD n₁] := by simpa [kb] using (Nat.chineseRemainder hcopn' b₁ b₀).2.1
      have hkb0 : kb ≡ b₀ [MOD n₀] := by simpa [kb] using (Nat.chineseRemainder hcopn' b₁ b₀).2.2
      have hkalt : ka < m₁ * m₀ := Nat.chineseRemainder_lt_mul hcopm' a₁ a₀ (ne_of_gt hm1) (ne_of_gt hm0)
      have hkblt : kb < n₁ * n₀ := Nat.chineseRemainder_lt_mul hcopn' b₁ b₀ (ne_of_gt hn1) (ne_of_gt hn0)
      have hka_lt : ka < m₀ * m₁ := by simpa [mul_comm m₁ m₀] using hkalt
      have hkb_lt : kb < n₀ * n₁ := by simpa [mul_comm n₁ n₀] using hkblt
      have hgcdka₀ : ka.gcd m₀ = 1 := by
        have hrm : ka % m₀ = a₀ := by
          calc
            ka % m₀ = a₀ % m₀ := hka0
            _ = a₀ := Nat.mod_eq_of_lt ha₀
        calc
          ka.gcd m₀ = (ka % m₀).gcd m₀ := (gcd_mod_left ka m₀).symm
          _ = a₀.gcd m₀ := by rw [hrm]
          _ = 1 := hgcd₀
      have hgcdka₁ : ka.gcd m₁ = 1 := by
        have hrm : ka % m₁ = a₁ := by
          calc
            ka % m₁ = a₁ % m₁ := hka1
            _ = a₁ := Nat.mod_eq_of_lt ha₁
        calc
          ka.gcd m₁ = (ka % m₁).gcd m₁ := (gcd_mod_left ka m₁).symm
          _ = a₁.gcd m₁ := by rw [hrm]
          _ = 1 := hgcd₁
      have hgcdkb₀ : kb.gcd n₀ = 1 := by
        have hrm : kb % n₀ = b₀ := by
          calc
            kb % n₀ = b₀ % n₀ := hkb0
            _ = b₀ := Nat.mod_eq_of_lt hb₀
        calc
          kb.gcd n₀ = (kb % n₀).gcd n₀ := (gcd_mod_left kb n₀).symm
          _ = b₀.gcd n₀ := by rw [hrm]
          _ = 1 := hgcdb₀
      have hgcdkb₁ : kb.gcd n₁ = 1 := by
        have hrm : kb % n₁ = b₁ := by
          calc
            kb % n₁ = b₁ % n₁ := hkb1
            _ = b₁ := Nat.mod_eq_of_lt hb₁
        calc
          kb.gcd n₁ = (kb % n₁).gcd n₁ := (gcd_mod_left kb n₁).symm
          _ = b₁.gcd n₁ := by rw [hrm]
          _ = 1 := hgcdb₁
      have hgcdka : ka.gcd (m₀ * m₁) = 1 := (gcd_mul_eq_one_iff hm01).mpr ⟨hgcdka₀, hgcdka₁⟩
      have hgcdkb : kb.gcd (n₀ * n₁) = 1 := (gcd_mul_eq_one_iff hn01).mpr ⟨hgcdkb₀, hgcdkb₁⟩
      -- congruence mod L0
      have hcong0a : (ka * X) % L₀ = (kb * Y + e) % L₀ := by
        calc
          (ka * X) % L₀ = (a₀ * X) % L₀ := mul_remainder_congr_of_mod hka0 h0m
          _ = (b₀ * Y + e) % L₀ := hcong₀
          _ = (kb * Y + e) % L₀ := (add_mul_remainder_congr_of_mod hkb0 h0n).symm
      -- congruence mod L1
      have hcong1a : (ka * X) % L₁ = (kb * Y + e) % L₁ := by
        calc
          (ka * X) % L₁ = (a₁ * X) % L₁ := mul_remainder_congr_of_mod hka1 h1m
          _ = (b₁ * Y + e) % L₁ := hcong₁
          _ = (kb * Y + e) % L₁ := (add_mul_remainder_congr_of_mod hkb1 h1n).symm
      have hcong : (ka * X) % (L₀ * L₁) = (kb * Y + e) % (L₀ * L₁) :=
        congr_eq_of_mul_modEq hcong0a hcong1a hL01
      have hmemab : (ka, kb) ∈ s := by
        rw [mem_FS]
        exact ⟨hka_lt, hgcdka, hkb_lt, hgcdkb, hcong⟩
      refine ⟨(ka, kb), hmemab, ?_⟩
      -- image equals x
      have hka0' : ka % m₀ = a₀ := by
        calc
          ka % m₀ = a₀ % m₀ := hka0
          _ = a₀ := Nat.mod_eq_of_lt ha₀
      have hka1' : ka % m₁ = a₁ := by
        calc
          ka % m₁ = a₁ % m₁ := hka1
          _ = a₁ := Nat.mod_eq_of_lt ha₁
      have hkb0' : kb % n₀ = b₀ := by
        calc
          kb % n₀ = b₀ % n₀ := hkb0
          _ = b₀ := Nat.mod_eq_of_lt hb₀
      have hkb1' : kb % n₁ = b₁ := by
        calc
          kb % n₁ = b₁ % n₁ := hkb1
          _ = b₁ := Nat.mod_eq_of_lt hb₁
      ext <;> simp [hka0', hka1', hkb0', hkb1', a₀, b₀, a₁, b₁]
  calc
    pairFiber (m₀ * m₁) (n₀ * n₁) X Y (L₀ * L₁) e = s.card := by
      simp [s, FS_card]
    _ = (s₀ ×ˢ s₁).card := hcard
    _ = s₀.card * s₁.card := Finset.card_product s₀ s₁
    _ = pairFiber m₀ n₀ X Y L₀ e * pairFiber m₁ n₁ X Y L₁ e := by
      simp [s₀, s₁, FS_card]

-- ============ product over prime factors ============

lemma coprime_pow_left_of_coprime {p k r : ℕ} (hp : p.Prime) (h : p.Coprime r) :
    (p ^ k).Coprime r := Nat.Coprime.pow_left k h

lemma coprime_pow_right_of_coprime {p k r : ℕ} (hp : p.Prime) (h : r.Coprime p) :
    r.Coprime (p ^ k) := Nat.Coprime.pow_right k h

lemma dvd_of_coprime_prime_left {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    p.Coprime q := (Nat.coprime_primes hp hq).mpr hne

/-- if p ∤ (n / p^e) where e = n.factorization p, then p is coprime to it -/
lemma prime_coprime_ordCompl {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p.Coprime (ordCompl[p] n) := Nat.coprime_ordCompl hp hn

lemma ordCompl_not_dvd_prime {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) : ¬ p ∣ ordCompl[p] n := by
  have hc : p.Coprime (ordCompl[p] n) := Nat.coprime_ordCompl hp hn
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hc

-- (m0 coprime ordCompl) with m0 = p^μ
lemma pow_coprime_ordCompl {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    (p ^ n.factorization p).Coprime (ordCompl[p] n) := by
  exact Nat.Coprime.pow_left (n.factorization p) (Nat.coprime_ordCompl hp hn)

lemma ordCompl_coprime_pow {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    (ordCompl[p] n).Coprime (p ^ n.factorization p) := by
  exact (pow_coprime_ordCompl (n := n) (p := p) hp hn).symm

lemma ordCompl_pow_mul {n p : ℕ} : p ^ n.factorization p * ordCompl[p] n = n :=
  Nat.ordProj_mul_ordCompl_eq_self n p

lemma ordCompl_pos' {n p : ℕ} (hn : n ≠ 0) : 0 < ordCompl[p] n := Nat.ordCompl_pos p hn

/-- primeFactors of ordCompl[p] n sit inside those of n -/
lemma primeFactors_ordCompl_subset {n p : ℕ} : (ordCompl[p] n).primeFactors ⊆ n.primeFactors := by
  intro q hq
  have hqm := Nat.mem_primeFactors.mp hq
  have hdiv : ordCompl[p] n ∣ n := Nat.ordCompl_dvd n p
  have hn0 : n ≠ 0 := by
    intro hz
    apply hqm.2.2
    rw [hz]
    simp
  exact Nat.mem_primeFactors.mpr ⟨hqm.1, dvd_trans hqm.2.1 hdiv, hn0⟩

/-- removing p from the modulus removes p from the complement's primes -/
lemma not_mem_primeFactors_ordCompl {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ∉ (ordCompl[p] n).primeFactors := by
  intro h
  exact ordCompl_not_dvd_prime hp hn (Nat.mem_primeFactors.mp h).2.1


/-- q prime dividing n with q ≠ p divides the ordCompl-part -/
lemma dvd_ordCompl_of_ne_prime {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p)
    (hqdn : q ∣ n) (hn : n ≠ 0) : q ∣ ordCompl[p] n := by
  have hqd : q ∣ ordCompl[p] n * p ^ n.factorization p := by
    have hq0 : q ∣ p ^ n.factorization p * ordCompl[p] n := by
      rw [Nat.ordProj_mul_ordCompl_eq_self n p]
      exact hqdn
    simpa [mul_comm] using hq0
  have hcop : q.Coprime (p ^ n.factorization p) := by
    have hpq : p.Coprime q := (Nat.coprime_primes hp hq).mpr (fun h => hne h.symm)
    exact (Nat.Coprime.pow_left (n.factorization p) hpq).symm
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop hqd

/-- ordCompl part of a nonzero n is nonzero -/
lemma ordCompl_ne_zero {n p : ℕ} (hn : n ≠ 0) : ordCompl[p] n ≠ 0 :=
  Nat.ne_of_gt (Nat.ordCompl_pos p hn)

/-- pairFiber over a modulus factors over its prime-power pieces -/
theorem pairFiber_eq_prod (m n X Y L e : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hL : 0 < L)
    (hLm : L ∣ m * X) (hLn : L ∣ n * Y)
    (hpm : m.primeFactors ⊆ L.primeFactors) (hpn : n.primeFactors ⊆ L.primeFactors) :
    pairFiber m n X Y L e =
      ∏ p ∈ L.primeFactors, pairFiber (p ^ m.factorization p) (p ^ n.factorization p) X Y
        (p ^ L.factorization p) e := by
  classical
  let P : ℕ → Prop := fun LL : ℕ =>
    ∀ (m n X Y e : ℕ), 0 < m → 0 < n → 0 < LL → LL ∣ m * X → LL ∣ n * Y →
      m.primeFactors ⊆ LL.primeFactors → n.primeFactors ⊆ LL.primeFactors →
        pairFiber m n X Y LL e = ∏ p ∈ LL.primeFactors,
          pairFiber (p ^ m.factorization p) (p ^ n.factorization p) X Y (p ^ LL.factorization p) e
  have hmain : ∀ LL : ℕ, (∀ r : ℕ, r < LL → P r) → P LL := by
    intro LL ih m n X Y e hm hn hLL hLm hLn hpm hpn
    by_cases hL1 : LL = 1
    · subst LL
      have hm1 : m = 1 := by
        by_contra h
        rcases Nat.exists_prime_and_dvd (n := m) h with ⟨q, hqp, hqd⟩
        have hqm : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqd, by omega⟩
        have hqL : q ∈ (1 : ℕ).primeFactors := hpm hqm
        simp at hqL
      have hn1 : n = 1 := by
        by_contra h
        rcases Nat.exists_prime_and_dvd (n := n) h with ⟨q, hqp, hqd⟩
        have hqn : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqd, by omega⟩
        have hqL : q ∈ (1 : ℕ).primeFactors := hpn hqn
        simp at hqL
      subst m
      subst n
      simp [pairFiber, FS]
      have hc : ∀ z ∈ ({(0, 0)} : Finset (ℕ × ℕ)), (z.1 * X) % 1 = (z.2 * Y + e) % 1 := by
        intro z hz
        have hz0 : z = (0, 0) := by simpa using (Finset.mem_singleton.mp hz)
        subst z
        simp [Nat.mod_one]
      rw [Finset.filter_eq_self.mpr hc]
      simp
    · have hLLne : LL ≠ 0 := by omega
      rcases Nat.exists_prime_and_dvd (n := LL) (by omega : LL ≠ 1) with ⟨p, pp, hpL⟩
      let eM : ℕ := m.factorization p
      let eN : ℕ := n.factorization p
      let eL : ℕ := LL.factorization p
      let m₀ : ℕ := p ^ eM
      let n₀ : ℕ := p ^ eN
      let d : ℕ := p ^ eL
      let rM : ℕ := ordCompl[p] m
      let rN : ℕ := ordCompl[p] n
      let rL : ℕ := ordCompl[p] LL
      have hLgt1 : 1 < LL := by omega
      have hd1 : 1 < d := by
        have heLpos : 0 < eL := by
          dsimp [eL]
          exact pp.factorization_pos_of_dvd hLLne hpL
        dsimp [d]
        have hp2 : 2 ≤ p := pp.two_le
        have hp_lt : p ≤ p ^ eL := by
          have hpow : p ^ 1 ≤ p ^ eL := Nat.pow_le_pow_right pp.pos heLpos
          simpa using hpow
        exact lt_of_lt_of_le (by omega : (1 : ℕ) < p) hp_lt
      have hm0 : 0 < m₀ := by
        dsimp [m₀]
        exact pow_pos pp.pos eM
      have hn0 : 0 < n₀ := by
        dsimp [n₀]
        exact pow_pos pp.pos eN
      have hd0 : 0 < d := by
        dsimp [d]
        exact pow_pos pp.pos eL
      have hrM0 : 0 < rM := by
        dsimp [rM]
        exact Nat.ordCompl_pos p (by omega : m ≠ 0)
      have hrN0 : 0 < rN := by
        dsimp [rN]
        exact Nat.ordCompl_pos p (by omega : n ≠ 0)
      have hrL0 : 0 < rL := by
        dsimp [rL]
        exact Nat.ordCompl_pos p hLLne
      have hm_prod : m₀ * rM = m := by
        dsimp [m₀, rM]
        exact Nat.ordProj_mul_ordCompl_eq_self m p
      have hn_prod : n₀ * rN = n := by
        dsimp [n₀, rN]
        exact Nat.ordProj_mul_ordCompl_eq_self n p
      have hL_prod : d * rL = LL := by
        dsimp [d, rL]
        exact Nat.ordProj_mul_ordCompl_eq_self LL p
      have hm01 : m₀.Coprime rM := by
        dsimp [m₀, rM]
        exact pow_coprime_ordCompl pp (by omega : m ≠ 0)
      have hn01 : n₀.Coprime rN := by
        dsimp [n₀, rN]
        exact pow_coprime_ordCompl pp (by omega : n ≠ 0)
      have hL01 : d.Coprime rL := by
        dsimp [d, rL]
        exact pow_coprime_ordCompl pp hLLne
      have h0m : d ∣ m₀ * X := by
        have h1 : d ∣ m * X := dvd_trans (by dsimp [d]; exact Nat.ordProj_dvd LL p) hLm
        have hmul : (m₀ * rM) * X = (m₀ * X) * rM := by ring
        have h1' : d ∣ (m₀ * rM) * X := by
          rwa [← hm_prod] at h1
        have h2 : d ∣ (m₀ * X) * rM := by
          rwa [hmul] at h1'
        have hcop : d.Coprime rM := by
          have hp1 : p.Coprime rM := by
            dsimp [rM]
            exact Nat.coprime_ordCompl pp (by omega : m ≠ 0)
          dsimp [d]
          exact Nat.Coprime.pow_left eL hp1
        exact Nat.Coprime.dvd_of_dvd_mul_right hcop h2
      have h0n : d ∣ n₀ * Y := by
        have h1 : d ∣ n * Y := dvd_trans (by dsimp [d]; exact Nat.ordProj_dvd LL p) hLn
        have hmul : (n₀ * rN) * Y = (n₀ * Y) * rN := by ring
        have h1' : d ∣ (n₀ * rN) * Y := by
          rwa [← hn_prod] at h1
        have h2 : d ∣ (n₀ * Y) * rN := by
          rwa [hmul] at h1'
        have hcop : d.Coprime rN := by
          have hp1 : p.Coprime rN := by
            dsimp [rN]
            exact Nat.coprime_ordCompl pp (by omega : n ≠ 0)
          dsimp [d]
          exact Nat.Coprime.pow_left eL hp1
        exact Nat.Coprime.dvd_of_dvd_mul_right hcop h2
      have h1m : rL ∣ rM * X := by
        have h1 : rL ∣ m * X := dvd_trans (by dsimp [rL]; exact Nat.ordCompl_dvd LL p) hLm
        have hmul : m * X = m₀ * (rM * X) := by
          rw [← hm_prod]
          ring
        have h2 : rL ∣ m₀ * (rM * X) := by
          rwa [hmul] at h1
        have hcop : rL.Coprime m₀ := by
          have hp1 : rL.Coprime p := by
            dsimp [rL]
            exact (Nat.coprime_ordCompl pp hLLne).symm
          dsimp [m₀]
          exact Nat.Coprime.pow_right eM hp1
        exact Nat.Coprime.dvd_of_dvd_mul_left hcop h2
      have h1n : rL ∣ rN * Y := by
        have h1 : rL ∣ n * Y := dvd_trans (by dsimp [rL]; exact Nat.ordCompl_dvd LL p) hLn
        have hmul : n * Y = n₀ * (rN * Y) := by
          rw [← hn_prod]
          ring
        have h2 : rL ∣ n₀ * (rN * Y) := by
          rwa [hmul] at h1
        have hcop : rL.Coprime n₀ := by
          have hp1 : rL.Coprime p := by
            dsimp [rL]
            exact (Nat.coprime_ordCompl pp hLLne).symm
          dsimp [n₀]
          exact Nat.Coprime.pow_right eN hp1
        exact Nat.Coprime.dvd_of_dvd_mul_left hcop h2
      have hpm' : rM.primeFactors ⊆ rL.primeFactors := by
        intro q hq
        have hqP : q.Prime := (Nat.mem_primeFactors.mp hq).1
        have hqM : q ∈ m.primeFactors := primeFactors_ordCompl_subset (n := m) hq
        have hqL0 : q ∈ LL.primeFactors := hpm hqM
        have hqL : q ∣ LL := (Nat.mem_primeFactors.mp hqL0).2.1
        have hqne : q ≠ p := by
          intro hpq
          subst q
          exact ordCompl_not_dvd_prime pp (by omega : m ≠ 0) (Nat.mem_primeFactors.mp hq).2.1
        have hqLd : q ∣ rL := by
          dsimp [rL]
          exact dvd_ordCompl_of_ne_prime pp hqP hqne hqL (by omega : LL ≠ 0)
        have hqcop : q.Coprime d := by
          have hpqc : p.Coprime q := (Nat.coprime_primes pp hqP).mpr (fun hpq => hqne hpq.symm)
          dsimp [d]
          exact (Nat.Coprime.pow_right eL hpqc.symm)
        exact Nat.mem_primeFactors.mpr ⟨hqP, hqLd, by
          simpa [rL] using ordCompl_ne_zero hLLne⟩
      have hpn' : rN.primeFactors ⊆ rL.primeFactors := by
        intro q hq
        have hqP : q.Prime := (Nat.mem_primeFactors.mp hq).1
        have hqN : q ∈ n.primeFactors := primeFactors_ordCompl_subset (n := n) hq
        have hqL0 : q ∈ LL.primeFactors := hpn hqN
        have hqL : q ∣ LL := (Nat.mem_primeFactors.mp hqL0).2.1
        have hqne : q ≠ p := by
          intro hpq
          subst q
          exact ordCompl_not_dvd_prime pp (by omega : n ≠ 0) (Nat.mem_primeFactors.mp hq).2.1
        have hqLd : q ∣ rL := by
          dsimp [rL]
          exact dvd_ordCompl_of_ne_prime pp hqP hqne hqL (by omega : LL ≠ 0)
        exact Nat.mem_primeFactors.mpr ⟨hqP, hqLd, by
          simpa [rL] using ordCompl_ne_zero hLLne⟩
      have hrLlt : rL < LL := by
        dsimp [rL]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hLLne) hd1
      have hih := ih rL hrLlt rM rN X Y e hrM0 hrN0 hrL0 h1m h1n hpm' hpn'
      have hsplit : pairFiber m n X Y LL e = pairFiber m₀ n₀ X Y d e * pairFiber rM rN X Y rL e := by
        calc
          pairFiber m n X Y LL e = pairFiber (m₀ * rM) (n₀ * rN) X Y (d * rL) e := by
            rw [← hm_prod, ← hn_prod, ← hL_prod]
          _ = pairFiber m₀ n₀ X Y d e * pairFiber rM rN X Y rL e :=
            pairFiber_mul m₀ rM n₀ rN X Y d rL e hm01 hn01 hL01 h0m h0n h1m h1n
              hm0 hrM0 hn0 hrN0 hd0 hrL0
      have hLpf : LL.primeFactors = insert p rL.primeFactors := by
        ext q
        constructor
        · intro hq
          by_cases hqeq : q = p
          · simp [hqeq]
          · have hq0 := Nat.mem_primeFactors.mp hq
            have hqLd : q ∣ rL := by
              dsimp [rL]
              exact dvd_ordCompl_of_ne_prime pp hq0.1 hqeq hq0.2.1 hLLne
            exact Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hq0.1, hqLd, by
              simpa [rL] using ordCompl_ne_zero hLLne⟩)
        · intro hq
          rw [Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact Nat.mem_primeFactors.mpr ⟨pp, hpL, hLLne⟩
          · have hq0 := Nat.mem_primeFactors.mp hq
            have hqLL : q ∈ LL.primeFactors := primeFactors_ordCompl_subset (n := LL) hq
            exact hqLL
      have hp_notin : p ∉ rL.primeFactors := by
        dsimp [rL]
        exact not_mem_primeFactors_ordCompl pp hLLne
      have hfp : pairFiber (p ^ m.factorization p) (p ^ n.factorization p) X Y (p ^ LL.factorization p) e
            = pairFiber m₀ n₀ X Y d e := by
          rfl
      have hfacM (q : ℕ) (hq : q ∈ rL.primeFactors) : q ^ rM.factorization q = q ^ m.factorization q := by
        have hqne : q ≠ p := by
          intro hqeq
          apply hp_notin
          rwa [hqeq] at hq
        have hfac : rM.factorization q = m.factorization q := by
          change (m / p ^ m.factorization p).factorization q = m.factorization q
          rw [Nat.factorization_ordCompl]
          rw [Finsupp.erase_ne hqne]
        rw [hfac]
      have hfacN (q : ℕ) (hq : q ∈ rL.primeFactors) : q ^ rN.factorization q = q ^ n.factorization q := by
        have hqne : q ≠ p := by
          intro hqeq
          apply hp_notin
          rwa [hqeq] at hq
        have hfac : rN.factorization q = n.factorization q := by
          change (n / p ^ n.factorization p).factorization q = n.factorization q
          rw [Nat.factorization_ordCompl]
          rw [Finsupp.erase_ne hqne]
        rw [hfac]
      have hfacL (q : ℕ) (hq : q ∈ rL.primeFactors) : q ^ rL.factorization q = q ^ LL.factorization q := by
        have hqne : q ≠ p := by
          intro hqeq
          apply hp_notin
          rwa [hqeq] at hq
        have hfac : rL.factorization q = LL.factorization q := by
          change (LL / p ^ LL.factorization p).factorization q = LL.factorization q
          rw [Nat.factorization_ordCompl]
          rw [Finsupp.erase_ne hqne]
        rw [hfac]
      have hprod : (∏ q ∈ LL.primeFactors,
          pairFiber (q ^ m.factorization q) (q ^ n.factorization q) X Y (q ^ LL.factorization q) e) =
          pairFiber m₀ n₀ X Y d e * (∏ q ∈ rL.primeFactors,
            pairFiber (q ^ rM.factorization q) (q ^ rN.factorization q) X Y (q ^ rL.factorization q) e) := by
        rw [hLpf, Finset.prod_insert hp_notin]
        rw [hfp]
        congr 1
        apply Finset.prod_congr rfl
        intro q hq
        rw [hfacM q hq, hfacN q hq, hfacL q hq]
      calc
        pairFiber m n X Y LL e = pairFiber m₀ n₀ X Y d e * pairFiber rM rN X Y rL e := hsplit
        _ = pairFiber m₀ n₀ X Y d e * (∏ q ∈ rL.primeFactors,
            pairFiber (q ^ rM.factorization q) (q ^ rN.factorization q) X Y (q ^ rL.factorization q) e) := by
              rw [hih]
        _ = ∏ q ∈ LL.primeFactors,
            pairFiber (q ^ m.factorization q) (q ^ n.factorization q) X Y (q ^ LL.factorization q) e := hprod.symm
  exact (Nat.strong_induction_on (p := P) L hmain) m n X Y e hm hn hL hLm hLn hpm hpn


-- ================== value of the local pieces ==================

-- ================== value of the local pieces ==================

/-- pairFiber over prime-power ranges equals the raw filtered product count -/
lemma pairFiber_prime_pow_raw (p μ ν X Y L e : ℕ) :
    pairFiber (p ^ μ) (p ^ ν) X Y L e =
      (((Finset.product (Finset.range (p ^ μ)) (Finset.range (p ^ ν))).filter
        (fun uv : ℕ × ℕ => uv.1.gcd (p ^ μ) = 1 ∧ uv.2.gcd (p ^ ν) = 1 ∧
          ((uv.1 * X) % L = ((uv.2 * Y + e) % L)))).card) := by
  unfold pairFiber
  congr 1
  ext uv
  simp [Finset.mem_product, Finset.mem_filter]
  tauto

/-- gcd filter over range p^k equals non-divisibility by p -/
lemma gcd_prime_pow_iff_not_dvd {p k x : ℕ} (hp : p.Prime) (hk : 0 < k) :
    x.gcd (p ^ k) = 1 ↔ ¬ p ∣ x := by
  rw [← Nat.coprime_iff_gcd_eq_one]
  rw [Nat.coprime_pow_right_iff hk x p, Nat.coprime_comm]
  exact hp.coprime_iff_not_dvd

/-- shared prime-power piece: X, Y units mod p -/
lemma pairFiber_shared_value (p k X Y e : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hX : ¬ p ∣ X) (hY : ¬ p ∣ Y) :
    pairFiber (p ^ k) (p ^ k) X Y (p ^ k) e =
      if p ∣ e then (p ^ k).totient else (p ^ k).totient - p ^ (k - 1) := by
  rw [pairFiber_prime_pow_raw p k k X Y (p ^ k) e]
  have hraw : (((Finset.product (Finset.range (p ^ k)) (Finset.range (p ^ k))).filter
        (fun uv : ℕ × ℕ => uv.1.gcd (p ^ k) = 1 ∧ uv.2.gcd (p ^ k) = 1 ∧
          ((uv.1 * X) % (p ^ k) = ((uv.2 * Y + e) % (p ^ k))))).card) =
      (((Finset.product (Finset.range (p ^ k)) (Finset.range (p ^ k))).filter
        (fun uv : ℕ × ℕ => ¬ p ∣ uv.1 ∧ ¬ p ∣ uv.2 ∧
          ((uv.1 * X) % (p ^ k) = ((uv.2 * Y + e) % (p ^ k))))).card) := by
    congr 1
    apply Finset.filter_congr
    intro uv huv
    rw [gcd_prime_pow_iff_not_dvd hp hk, gcd_prime_pow_iff_not_dvd hp hk]
  rw [hraw]
  exact Commons.NumberTheory.DuffinSchaeffer.reduced_pair_count_prime_pow p k X Y e hp hk hX hY

/-- fresh prime power piece, M-side carries p^b -/
lemma pairFiber_freshM_value (p a b N M e : ℕ) (hp : p.Prime) (hb : 0 < b)
    (hN : ¬ p ∣ N) (hM : p ^ b ∣ M) (hM' : ¬ p ∣ M / p ^ b) :
    pairFiber (p ^ (a + b)) (p ^ a) N M (p ^ (a + b)) e =
      if p ∣ e then 0 else (p ^ a).totient := by
  have hM_eq : M = p ^ b * (M / p ^ b) := by
    calc
      M = (M / p ^ b) * p ^ b := (Nat.div_mul_cancel hM).symm
      _ = p ^ b * (M / p ^ b) := Nat.mul_comm (M / p ^ b) (p ^ b)
  have hrew : pairFiber (p ^ (a + b)) (p ^ a) N M (p ^ (a + b)) e =
      pairFiber (p ^ (a + b)) (p ^ a) N (p ^ b * (M / p ^ b)) (p ^ (a + b)) e := by
    rw [hM_eq.symm]
  rw [hrew]
  rw [pairFiber_prime_pow_raw p (a + b) a N (p ^ b * (M / p ^ b)) (p ^ (a + b)) e]
  exact Commons.Data.Nat.pair_count_freshM p a b N (M / p ^ b) e hp hb hN hM'


/-- (n - e % n) + e is a multiple of n -/
lemma mod_add_sub_mod_eq_zero (e n : ℕ) (hn : 0 < n) : ((n - e % n) + e) % n = 0 := by
  have hme : e ≡ e % n [MOD n] := by
    change e % n = (e % n) % n
    exact (Nat.mod_mod e n).symm
  have h2 : (n - e % n) + e ≡ (n - e % n) + e % n [MOD n] := Nat.ModEq.add_left (n - e % n) hme
  have h3 : (n - e % n) + e ≡ n [MOD n] := by
    have hle : e % n ≤ n := le_of_lt (Nat.mod_lt e hn)
    have h1 : (n - e % n) + e % n = n := Nat.sub_add_cancel hle
    simpa [h1] using h2
  have h4 : n ≡ 0 [MOD n] := by simp [Nat.ModEq]
  simpa [Nat.ModEq] using (h3.trans h4)

/-- congruence sign flip: if t ≡ -e (mod n), then a ≡ b + e iff b ≡ a + t -/
lemma mod_eq_iff_add_mod (a b e t n : ℕ) (hte : (t + e) % n = 0) :
    a % n = (b + e) % n ↔ b % n = (a + t) % n := by
  constructor
  · intro h
    have hME : a ≡ b + e [MOD n] := h
    have hteME : t + e ≡ 0 [MOD n] := by
      change (t + e) % n = 0 % n
      simpa using hte
    have h1 : a + t ≡ b + (t + e) [MOD n] := by
      have h1' : a + t ≡ (b + e) + t [MOD n] := Nat.ModEq.add_right t hME
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1'
    have h2 : b + (t + e) ≡ b [MOD n] := by
      have h2' : b + (t + e) ≡ b + 0 [MOD n] := Nat.ModEq.add_left b hteME
      simpa using h2'
    exact (h1.trans h2).symm
  · intro h
    have hME : b ≡ a + t [MOD n] := h
    have hteME : t + e ≡ 0 [MOD n] := by
      change (t + e) % n = 0 % n
      simpa using hte
    have h1 : b + e ≡ a + (t + e) [MOD n] := by
      have h1' : b + e ≡ (a + t) + e [MOD n] := Nat.ModEq.add_right e hME
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1'
    have h2 : a + (t + e) ≡ a [MOD n] := by
      have h2' : a + (t + e) ≡ a + 0 [MOD n] := Nat.ModEq.add_left a hteME
      simpa using h2'
    exact (h1.trans h2).symm

/-- p divides n - e % n iff p divides e (when p | n, n > 0) -/
lemma dvd_sub_mod_iff_dvd (p e n : ℕ) (hn : 0 < n) (hpn : p ∣ n) :
    p ∣ n - e % n ↔ p ∣ e := by
  have hme : e ≡ e % n [MOD n] := by
    change e % n = (e % n) % n
    exact (Nat.mod_mod e n).symm
  have hmp : e ≡ e % n [MOD p] := Nat.ModEq.of_dvd hpn hme
  have hpe_iff : p ∣ e ↔ p ∣ e % n := Nat.ModEq.dvd_iff hmp (dvd_refl p)
  constructor
  · intro hpt
    have hpemod : p ∣ e % n := by
      have h3 : p ∣ n - (n - e % n) := Nat.dvd_sub hpn hpt
      have hsub : n - (n - e % n) = e % n := by
        have hle : e % n ≤ n := le_of_lt (Nat.mod_lt e hn)
        omega
      rwa [hsub] at h3
    exact hpe_iff.mpr hpemod
  · intro hpe
    have hpemod : p ∣ e % n := hpe_iff.mp hpe
    exact Nat.dvd_sub hpn hpemod

/-- generic: transposing coordinates preserves the card of a filter -/
lemma filter_swap_card {α β : Type*} (A : Finset α) (B : Finset β)
    (P : α → β → Prop) (Q : β → α → Prop)
    [DecidablePred (fun ab : α × β => P ab.1 ab.2)]
    [DecidablePred (fun ba : β × α => Q ba.1 ba.2)]
    (hiff : ∀ a b, P a b ↔ Q b a) :
    ((A.product B).filter (fun ab : α × β => P ab.1 ab.2)).card =
    ((B.product A).filter (fun ba : β × α => Q ba.1 ba.2)).card := by
  classical
  refine Finset.card_bij' (s := (A.product B).filter (fun ab : α × β => P ab.1 ab.2))
    (t := (B.product A).filter (fun ba : β × α => Q ba.1 ba.2))
    (fun ab _ => (ab.2, ab.1)) (fun ba _ => (ba.2, ba.1)) ?hi ?hj ?li ?ri
  · intro ab hab
    rw [Finset.mem_filter] at hab
    rcases hab with ⟨hprod, hP⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rcases (Finset.mem_product.mp hprod) with ⟨ha, hb⟩
      exact Finset.mem_product.mpr ⟨hb, ha⟩
    · exact (hiff ab.1 ab.2).mp hP
  · intro ba hba
    rw [Finset.mem_filter] at hba
    rcases hba with ⟨hprod, hQ⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rcases (Finset.mem_product.mp hprod) with ⟨hb, ha⟩
      exact Finset.mem_product.mpr ⟨ha, hb⟩
    · exact (hiff ba.2 ba.1).mpr hQ
  · intro ab hab
    ext <;> rfl
  · intro ba hba
    ext <;> rfl

/-- the freshN raw count equals the transposed freshM raw count with e replaced by t ≡ -e -/
lemma freshN_card_eq_freshM (p a b R S e t : ℕ) (hp : p.Prime)
    (hte : (t + e) % (p ^ (a + b)) = 0) :
    (((Finset.product (Finset.range (p ^ a)) (Finset.range (p ^ (a + b)))).filter
      (fun uv : ℕ × ℕ => uv.1.gcd (p ^ a) = 1 ∧ uv.2.gcd (p ^ (a + b)) = 1 ∧
        ((uv.1 * (p ^ b * R)) % (p ^ (a + b)) = ((uv.2 * S + e) % (p ^ (a + b)))))).card) =
    (((Finset.product (Finset.range (p ^ (a + b))) (Finset.range (p ^ a))).filter
      (fun uv : ℕ × ℕ => uv.1.gcd (p ^ (a + b)) = 1 ∧ uv.2.gcd (p ^ a) = 1 ∧
        ((uv.1 * S) % (p ^ (a + b)) = ((uv.2 * (p ^ b * R) + t) % (p ^ (a + b)))))).card) := by
  classical
  let n : ℕ := p ^ (a + b)
  have hn0 : 0 < n := by dsimp [n]; exact pow_pos hp.pos (a + b)
  have hte' : (t + e) % n = 0 := by simpa [n] using hte
  have hiff : ∀ u v : ℕ,
      (u.gcd (p ^ a) = 1 ∧ v.gcd n = 1 ∧ (u * (p ^ b * R)) % n = (v * S + e) % n) ↔
      (v.gcd n = 1 ∧ u.gcd (p ^ a) = 1 ∧ (v * S) % n = (u * (p ^ b * R) + t) % n) := by
    intro u v
    rw [mod_eq_iff_add_mod (a := u * (p ^ b * R)) (b := v * S) e t n hte']
    tauto
  simpa [n] using (filter_swap_card (A := Finset.range (p ^ a)) (B := Finset.range n)
    (P := fun u v : ℕ => u.gcd (p ^ a) = 1 ∧ v.gcd n = 1 ∧
      (u * (p ^ b * R)) % n = (v * S + e) % n)
    (Q := fun v u : ℕ => v.gcd n = 1 ∧ u.gcd (p ^ a) = 1 ∧
      (v * S) % n = (u * (p ^ b * R) + t) % n) hiff)

/-- freshN value at the raw-count level: coprime pairs (u < p^a, v < p^(a+b))
with u·(p^b·R) ≡ v·S + e (mod p^(a+b)) -/
theorem pair_count_freshN (p a b R S e : ℕ) (hp : p.Prime) (hb : 0 < b)
    (hR : ¬ p ∣ R) (hS : ¬ p ∣ S) :
    (((Finset.product (Finset.range (p ^ a)) (Finset.range (p ^ (a + b)))).filter
      (fun uv : ℕ × ℕ => uv.1.gcd (p ^ a) = 1 ∧ uv.2.gcd (p ^ (a + b)) = 1 ∧
        ((uv.1 * (p ^ b * R)) % (p ^ (a + b)) = ((uv.2 * S + e) % (p ^ (a + b)))))).card) =
      if p ∣ e then 0 else (p ^ a).totient := by
  classical
  let n : ℕ := p ^ (a + b)
  have hn0 : 0 < n := by dsimp [n]; exact pow_pos hp.pos (a + b)
  let t : ℕ := n - e % n
  have hte : (t + e) % n = 0 := by
    dsimp [t]
    exact mod_add_sub_mod_eq_zero e n hn0
  have hte0 : (t + e) % (p ^ (a + b)) = 0 := by simpa [n] using hte
  have hcard := freshN_card_eq_freshM p a b R S e t hp hte0
  have hpt : p ∣ t ↔ p ∣ e := by
    dsimp [t, n]
    have hpn : p ∣ p ^ (a + b) := by
      simpa using (pow_dvd_pow p (show 1 ≤ a + b by omega) : p ^ 1 ∣ p ^ (a + b))
    exact dvd_sub_mod_iff_dvd p e (p ^ (a + b)) (pow_pos hp.pos (a + b)) hpn
  by_cases hpe : p ∣ e
  · rw [if_pos hpe, hcard]
    rw [Commons.Data.Nat.pair_count_freshM p a b S R t hp hb hS hR]
    rw [if_pos (hpt.mpr hpe)]
  · rw [if_neg hpe, hcard]
    rw [Commons.Data.Nat.pair_count_freshM p a b S R t hp hb hS hR]
    rw [if_neg (fun hpt' : p ∣ t => hpe (hpt.mp hpt'))]

lemma pairFiber_freshN_value (p a b N M e : ℕ) (hp : p.Prime) (hb : 0 < b)
    (hN : p ^ b ∣ N) (hN' : ¬ p ∣ N / p ^ b) (hM : ¬ p ∣ M) :
    pairFiber (p ^ a) (p ^ (a + b)) N M (p ^ (a + b)) e =
      if p ∣ e then 0 else (p ^ a).totient := by
  have hN_eq : N = p ^ b * (N / p ^ b) := by
    calc
      N = (N / p ^ b) * p ^ b := (Nat.div_mul_cancel hN).symm
      _ = p ^ b * (N / p ^ b) := Nat.mul_comm (N / p ^ b) (p ^ b)
  have hrew : pairFiber (p ^ a) (p ^ (a + b)) N M (p ^ (a + b)) e =
      pairFiber (p ^ a) (p ^ (a + b)) (p ^ b * (N / p ^ b)) M (p ^ (a + b)) e := by
    rw [hN_eq.symm]
  rw [hrew]
  rw [pairFiber_prime_pow_raw p a (a + b) (p ^ b * (N / p ^ b)) M (p ^ (a + b)) e]
  exact pair_count_freshN p a b (N / p ^ b) M e hp hb hN' hM

/-- when gcd(e, q) ≠ 1 (with q = M*N) the count is 0 -/
lemma pairFiber_zero_of_not_coprime_q (m n e : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hnot : ¬ e.gcd ((m / m.gcd n) * (n / m.gcd n)) = 1) :
    pairFiber m n (n / m.gcd n) (m / m.gcd n) (m * n / m.gcd n) e = 0 := by
  classical
  let g : ℕ := m.gcd n
  let M : ℕ := m / g
  let N : ℕ := n / g
  let L : ℕ := m * n / g
  have hg0 : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left n hm
  have hgm : g ≤ m := by
    dsimp [g]
    exact Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)
  have hgn : g ≤ n := by
    dsimp [g]
    exact Nat.le_of_dvd hn (Nat.gcd_dvd_right m n)
  have hq0 : 0 < M * N := by
    dsimp [M, N]
    exact mul_pos (Nat.div_pos hgm hg0) (Nat.div_pos hgn hg0)
  have hgnot1 : e.gcd (M * N) ≠ 1 := by
    simpa [M, N, g] using hnot
  have hgeq2 : 2 ≤ e.gcd (M * N) := by
    have hg1 : 1 ≤ e.gcd (M * N) := Nat.gcd_pos_of_pos_right e hq0
    by_contra h
    have hle : e.gcd (M * N) ≤ 1 := by omega
    have : e.gcd (M * N) = 1 := by omega
    exact hgnot1 this
  rcases Nat.exists_prime_and_dvd (n := e.gcd (M * N)) (by omega : e.gcd (M * N) ≠ 1) with ⟨p, pp, hpg⟩
  have hpe : p ∣ e := dvd_trans hpg (Nat.gcd_dvd_left e (M * N))
  have hpq : p ∣ M * N := dvd_trans hpg (Nat.gcd_dvd_right e (M * N))
  have hMdvdm : M ∣ m := by
    dsimp [M]
    exact ⟨g, (Nat.div_mul_cancel (Nat.gcd_dvd_left m n)).symm⟩
  have hNdvdn : N ∣ n := by
    dsimp [N]
    exact ⟨g, (Nat.div_mul_cancel (Nat.gcd_dvd_right m n)).symm⟩
  have hcopMN : M.Coprime N := by
    dsimp [M, N]
    exact Nat.coprime_div_gcd_div_gcd hg0
  by_cases hpM : p ∣ M
  · have hpN : ¬ p ∣ N := by
      intro hpNd
      have hp1 : p ∣ 1 := by
        have hpgcd : p ∣ M.gcd N := Nat.dvd_gcd hpM hpNd
        have hg1 : M.gcd N = 1 := hcopMN.gcd_eq_one
        rwa [hg1] at hpgcd
      exact pp.not_dvd_one hp1
    by_contra hne0
    have hpos : 0 < pairFiber m n N M L e := Nat.pos_of_ne_zero hne0
    rcases Finset.card_pos.mp (by simpa [pairFiber, FS] using hpos) with ⟨ab, hab⟩
    rcases mem_FS.mp hab with ⟨ham, hgm', hbn, hgn', hcong⟩
    have hpL : p ∣ L := by
      have hLN : L = m * N := by
        dsimp [L, N, g]
        exact Nat.mul_div_assoc m (Nat.gcd_dvd_right m n)
      rw [hLN]
      exact dvd_mul_of_dvd_left (dvd_trans hpM hMdvdm) N
    have hmodp : (ab.1 * N) % p = (ab.2 * M + e) % p := by
      calc
        (ab.1 * N) % p = ((ab.1 * N) % L) % p := (Nat.mod_mod_of_dvd (ab.1 * N) hpL).symm
        _ = ((ab.2 * M + e) % L) % p := by rw [hcong]
        _ = (ab.2 * M + e) % p := Nat.mod_mod_of_dvd (ab.2 * M + e) hpL
    have hpR : p ∣ ab.2 * M + e := Nat.dvd_add (dvd_mul_of_dvd_right hpM ab.2) hpe
    have hpLHS : p ∣ ab.1 * N := by
      rw [Nat.dvd_iff_mod_eq_zero, hmodp]
      exact Nat.mod_eq_zero_of_dvd hpR
    have hpa : p ∣ ab.1 := by
      rcases (Nat.Prime.dvd_mul (m := ab.1) (n := N) pp).mp hpLHS with h | h
      · exact h
      · exact False.elim (hpN h)
    have hpg1 : p ∣ ab.1.gcd m := Nat.dvd_gcd hpa (dvd_trans hpM hMdvdm)
    have h1 : p ∣ 1 := by rwa [hgm'] at hpg1
    exact pp.not_dvd_one h1
  · have hpN : p ∣ N := by
      rcases (Nat.Prime.dvd_mul (m := M) (n := N) pp).mp hpq with h | h
      · exact False.elim (hpM h)
      · exact h
    by_contra hne0
    have hpos : 0 < pairFiber m n N M L e := Nat.pos_of_ne_zero hne0
    rcases Finset.card_pos.mp (by simpa [pairFiber, FS] using hpos) with ⟨ab, hab⟩
    rcases mem_FS.mp hab with ⟨ham, hgm', hbn, hgn', hcong⟩
    have hpL : p ∣ L := by
      have hLM : L = M * n := by
        dsimp [L, M, g]
        calc
          m * n / (m.gcd n) = n * m / (m.gcd n) := by rw [mul_comm]
          _ = n * (m / m.gcd n) := Nat.mul_div_assoc n (Nat.gcd_dvd_left m n)
          _ = (m / m.gcd n) * n := by rw [mul_comm]
      rw [hLM]
      exact dvd_mul_of_dvd_right (dvd_trans hpN hNdvdn) M
    have hmodp : (ab.2 * M + e) % p = (ab.1 * N) % p := by
      calc
        (ab.2 * M + e) % p = ((ab.2 * M + e) % L) % p := (Nat.mod_mod_of_dvd (ab.2 * M + e) hpL).symm
        _ = ((ab.1 * N) % L) % p := by rw [hcong]
        _ = (ab.1 * N) % p := Nat.mod_mod_of_dvd (ab.1 * N) hpL
    have hpLHS : p ∣ ab.2 * M + e := by
      rw [Nat.dvd_iff_mod_eq_zero, hmodp]
      exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hpN ab.1)
    have hbM : p ∣ ab.2 * M := by
      have hsub : p ∣ (ab.2 * M + e) - e := Nat.dvd_sub hpLHS hpe
      have : (ab.2 * M + e) - e = ab.2 * M := Nat.add_sub_cancel (ab.2 * M) e
      rwa [this] at hsub
    have hpb : p ∣ ab.2 := by
      rcases (Nat.Prime.dvd_mul (m := ab.2) (n := M) pp).mp hbM with h | h
      · exact h
      · exact False.elim (hpM h)
    have hpg1 : p ∣ ab.2.gcd n := Nat.dvd_gcd hpb (dvd_trans hpN hNdvdn)
    have h1 : p ∣ 1 := by rwa [hgn'] at hpg1
    exact pp.not_dvd_one h1

/-- gcd factorization at a prime is the min -/
lemma rf_g_fact_min (m n p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m.gcd n).factorization p = min (m.factorization p) (n.factorization p) := by
  rw [Nat.factorization_gcd hm hn]
  rfl

/-- lcm factorization at a prime is the max -/
lemma rf_lcm_fact_max (m n p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (Nat.lcm m n).factorization p = max (m.factorization p) (n.factorization p) := by
  rw [Nat.factorization_lcm hm hn]
  rfl

/-- (m*n/gcd).factorization at a prime is the max -/
lemma rf_L_fact_max (m n p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n / m.gcd n).factorization p = max (m.factorization p) (n.factorization p) := by
  have hL : m * n / m.gcd n = Nat.lcm m n := by
    calc m * n / m.gcd n = m * (n / m.gcd n) := Nat.mul_div_assoc m (Nat.gcd_dvd_right m n)
      _ = Nat.lcm m n := Commons.Data.Nat.mul_div_gcd_eq_lcm m n
  rw [hL]
  exact rf_lcm_fact_max m n p hm hn

/-- if κ = min α β and κ < α then β < α and κ = β -/
lemma rf_min_lt_of_lt {α β κ : ℕ} (hκ : κ = min α β) (hlt : κ < α) : β < α ∧ κ = β := by
  by_cases hαβ : α ≤ β
  · exfalso
    have hmin : min α β = α := min_eq_left hαβ
    have hκa : κ = α := by rw [hκ, hmin]
    omega
  · have hβα : β < α := by omega
    have hκβ : κ = β := by rw [hκ, min_eq_right (le_of_lt hβα)]
    exact ⟨hβα, hκβ⟩

/-- M-side prime piece: p divides M (= m/g). -/
lemma rf_piece_qM (m n e p : ℕ) (hm : 0 < m) (hn : 0 < n) (hp : p.Prime)
    (hpM : p ∣ m / m.gcd n) :
    pairFiber (p ^ m.factorization p) (p ^ n.factorization p) (n / m.gcd n) (m / m.gcd n)
      (p ^ (m * n / m.gcd n).factorization p) e =
      if p ∣ e then 0 else (p ^ (m.gcd n).factorization p).totient := by
  classical
  let M : ℕ := m / m.gcd n
  let N : ℕ := n / m.gcd n
  have hM0 : 0 < M := by
    dsimp [M]
    exact Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)) (Nat.gcd_pos_of_pos_left n hm)
  have hN0 : 0 < N := by
    dsimp [N]
    exact Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right m n)) (Nat.gcd_pos_of_pos_left n hm)
  let α : ℕ := m.factorization p
  let β : ℕ := n.factorization p
  let κ : ℕ := (m.gcd n).factorization p
  let lam : ℕ := (m * n / m.gcd n).factorization p
  have hκ : κ = min α β := by dsimp [κ, α, β]; exact rf_g_fact_min m n p hm.ne' hn.ne'
  have hlam : lam = max α β := by dsimp [lam, α, β]; exact rf_L_fact_max m n p hm.ne' hn.ne'
  have hMf : M.factorization p = α - κ := by
    dsimp [M, α, κ]
    rw [Nat.factorization_div (Nat.gcd_dvd_left m n)]
    rfl
  have hMfpos : 0 < M.factorization p := by
    have h1 : 1 ≤ M.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hM0.ne').mp (by simpa [M] using hpM)
    omega
  have hκlt : κ < α := by
    have : 0 < α - κ := by simpa [hMf] using hMfpos
    omega
  have ⟨hβα, hκβ⟩ := rf_min_lt_of_lt (α := α) (β := β) (κ := κ) hκ hκlt
  have hNnd : ¬ p ∣ N := by
    have hNf : N.factorization p = 0 := by
      have hsub : N.factorization p = β - κ := by
        dsimp [N, β, κ]
        rw [Nat.factorization_div (Nat.gcd_dvd_right m n)]
        rfl
      rw [hsub, hκβ]
      simp
    intro hpd
    have h1 : 1 ≤ N.factorization p := (Nat.Prime.dvd_iff_one_le_factorization hp hN0.ne').mp hpd
    omega
  have hb : 0 < α - β := by omega
  have hb_eq : α - β = M.factorization p := by
    calc α - β = α - κ := by rw [hκβ]
      _ = M.factorization p := hMf.symm
  have hM1 : p ^ (α - β) ∣ M := by
    simpa [hb_eq] using (Nat.ordProj_dvd M p)
  have hM2 : ¬ p ∣ M / p ^ (α - β) := by
    intro hd
    have hd' : ¬ p ∣ M / p ^ M.factorization p := Nat.not_dvd_ordCompl hp hM0.ne'
    have hd'' : p ∣ M / p ^ M.factorization p := by simpa [hb_eq] using hd
    exact hd' hd''
  have hlam' : lam = β + (α - β) := by
    have : lam = α := by
      rw [hlam, max_eq_left (le_of_lt hβα)]
    rw [this]
    omega
  have ham : m.factorization p = β + (α - β) := by omega
  -- rewrite exponents in the pairFiber to freshM shape
  rw [ham]
  rw [show (m * n / m.gcd n).factorization p = β + (α - β) from hlam']
  rw [pairFiber_freshM_value p β (α - β) N M e hp hb hNnd hM1 hM2]
  by_cases hpe : p ∣ e
  · rw [if_pos hpe, if_pos hpe]
  · rw [if_neg hpe, if_neg hpe]
    congr 1
    have hβg : (m.gcd n).factorization p = β := by
      dsimp [κ] at hκβ
      exact hκβ
    rw [hβg]

/-- N-side prime piece: p divides N (= n/g). -/
lemma rf_piece_qN (m n e p : ℕ) (hm : 0 < m) (hn : 0 < n) (hp : p.Prime)
    (hpN : p ∣ n / m.gcd n) :
    pairFiber (p ^ m.factorization p) (p ^ n.factorization p) (n / m.gcd n) (m / m.gcd n)
      (p ^ (m * n / m.gcd n).factorization p) e =
      if p ∣ e then 0 else (p ^ (m.gcd n).factorization p).totient := by
  classical
  let M : ℕ := m / m.gcd n
  let N : ℕ := n / m.gcd n
  have hM0 : 0 < M := by
    dsimp [M]
    exact Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)) (Nat.gcd_pos_of_pos_left n hm)
  have hN0 : 0 < N := by
    dsimp [N]
    exact Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right m n)) (Nat.gcd_pos_of_pos_left n hm)
  let α : ℕ := m.factorization p
  let β : ℕ := n.factorization p
  let κ : ℕ := (m.gcd n).factorization p
  let lam : ℕ := (m * n / m.gcd n).factorization p
  have hκ : κ = min α β := by dsimp [κ, α, β]; exact rf_g_fact_min m n p hm.ne' hn.ne'
  have hlam : lam = max α β := by dsimp [lam, α, β]; exact rf_L_fact_max m n p hm.ne' hn.ne'
  have hNf : N.factorization p = β - κ := by
    dsimp [N, β, κ]
    rw [Nat.factorization_div (Nat.gcd_dvd_right m n)]
    rfl
  have hNfpos : 0 < N.factorization p := by
    have h1 : 1 ≤ N.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hN0.ne').mp (by simpa [N] using hpN)
    omega
  have hκlt : κ < β := by
    have : 0 < β - κ := by simpa [hNf] using hNfpos
    omega
  have hκlt' : κ < β := hκlt
  -- min α β < β implies α < β and κ = α
  have hαβlt : α < β ∧ κ = α := by
    -- use rf_min_lt_of_lt-like reasoning with roles swapped: min α β < β → α < β
    rcases rf_min_lt_of_lt (α := β) (β := α) (κ := κ) (by rw [min_comm]; exact hκ) hκlt' with ⟨hαβ, hκα⟩
    exact ⟨hαβ, hκα⟩
  rcases hαβlt with ⟨hαβ, hκα⟩
  have hMnd : ¬ p ∣ M := by
    have hMf : M.factorization p = 0 := by
      have hsub : M.factorization p = α - κ := by
        dsimp [M, α, κ]
        rw [Nat.factorization_div (Nat.gcd_dvd_left m n)]
        rfl
      rw [hsub, hκα]
      simp
    intro hpd
    have h1 : 1 ≤ M.factorization p := (Nat.Prime.dvd_iff_one_le_factorization hp hM0.ne').mp hpd
    omega
  have hb : 0 < β - α := by omega
  have hb_eq : β - α = N.factorization p := by
    calc β - α = β - κ := by rw [hκα]
      _ = N.factorization p := hNf.symm
  have hN1 : p ^ (β - α) ∣ N := by
    simpa [hb_eq] using (Nat.ordProj_dvd N p)
  have hN2 : ¬ p ∣ N / p ^ (β - α) := by
    intro hd
    have hd' : ¬ p ∣ N / p ^ N.factorization p := Nat.not_dvd_ordCompl hp hN0.ne'
    have hd'' : p ∣ N / p ^ N.factorization p := by simpa [hb_eq] using hd
    exact hd' hd''
  have hlam' : lam = α + (β - α) := by
    have : lam = β := by
      rw [hlam, max_eq_right (le_of_lt hαβ)]
    rw [this]
    omega
  have hbn : n.factorization p = α + (β - α) := by omega
  -- rewrite exponents in the pairFiber to freshN shape
  rw [hbn]
  rw [show (m * n / m.gcd n).factorization p = α + (β - α) from hlam']
  rw [pairFiber_freshN_value p α (β - α) N M e hp hb hN1 hN2 hMnd]
  by_cases hpe : p ∣ e
  · rw [if_pos hpe, if_pos hpe]
  · rw [if_neg hpe, if_neg hpe]
    congr 1
    have hαg : (m.gcd n).factorization p = α := by
      dsimp [κ] at hκα
      exact hκα
    rw [hαg]

/-- K-side prime piece: p | g (= gcd) and p does not divide q (= M*N), so the
exponents of p in m and n are equal: the shared case. -/
lemma rf_piece_K (m n e p : ℕ) (hm : 0 < m) (hn : 0 < n) (hp : p.Prime)
    (hpg : p ∣ m.gcd n) (hpq : ¬ p ∣ (m / m.gcd n) * (n / m.gcd n)) :
    pairFiber (p ^ m.factorization p) (p ^ n.factorization p) (n / m.gcd n) (m / m.gcd n)
      (p ^ (m * n / m.gcd n).factorization p) e =
      if p ∣ e then (p ^ (m.gcd n).factorization p).totient
      else (p ^ (m.gcd n).factorization p).totient - p ^ ((m.gcd n).factorization p - 1) := by
  classical
  let M : ℕ := m / m.gcd n
  let N : ℕ := n / m.gcd n
  have hM0 : 0 < M := by
    dsimp [M]
    exact Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)) (Nat.gcd_pos_of_pos_left n hm)
  have hN0 : 0 < N := by
    dsimp [N]
    exact Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right m n)) (Nat.gcd_pos_of_pos_left n hm)
  let κ : ℕ := (m.gcd n).factorization p
  let α : ℕ := m.factorization p
  let β : ℕ := n.factorization p
  let lam : ℕ := (m * n / m.gcd n).factorization p
  have hκpos : 0 < κ := by
    have h1 : 1 ≤ κ := by
      dsimp [κ]
      exact (Nat.Prime.dvd_iff_one_le_factorization hp (Nat.gcd_pos_of_pos_left n hm).ne').mp hpg
    omega
  have hMnd : ¬ p ∣ M := by
    intro hd
    exact hpq (dvd_mul_of_dvd_left hd N)
  have hNnd : ¬ p ∣ N := by
    intro hd
    exact hpq (dvd_mul_of_dvd_right hd M)
  have hMf0 : M.factorization p = 0 := by
    have hnf : ¬ 1 ≤ M.factorization p := by
      intro h1
      exact hMnd ((Nat.Prime.dvd_iff_one_le_factorization hp hM0.ne').mpr h1)
    omega
  have hNf0 : N.factorization p = 0 := by
    have hnf : ¬ 1 ≤ N.factorization p := by
      intro h1
      exact hNnd ((Nat.Prime.dvd_iff_one_le_factorization hp hN0.ne').mpr h1)
    omega
  have hακ : α = κ := by
    have hsub : M.factorization p = α - κ := by
      dsimp [M, α, κ]
      rw [Nat.factorization_div (Nat.gcd_dvd_left m n)]
      rfl
    have hle : κ ≤ α := by
      dsimp [κ, α]
      rw [rf_g_fact_min m n p hm.ne' hn.ne']
      exact min_le_left (m.factorization p) (n.factorization p)
    have h0 : α - κ = 0 := by simpa [hsub] using hMf0
    omega
  have hβκ : β = κ := by
    have hsub : N.factorization p = β - κ := by
      dsimp [N, β, κ]
      rw [Nat.factorization_div (Nat.gcd_dvd_right m n)]
      rfl
    have hle : κ ≤ β := by
      dsimp [κ, β]
      rw [rf_g_fact_min m n p hm.ne' hn.ne']
      exact min_le_right (m.factorization p) (n.factorization p)
    have h0 : β - κ = 0 := by simpa [hsub] using hNf0
    omega
  have hlamκ : lam = κ := by
    have hmax : max α β = κ := by
      rw [hακ, hβκ]
      simp
    have hlam : lam = max α β := by dsimp [lam, α, β]; exact rf_L_fact_max m n p hm.ne' hn.ne'
    rw [hlam, hmax]
  have hmg : m.factorization p = κ := by simpa [α] using hακ
  have hng : n.factorization p = κ := by simpa [β] using hβκ
  -- rewrite exponents
  rw [hmg, hng]
  rw [show (m * n / m.gcd n).factorization p = κ from hlamκ]
  rw [pairFiber_shared_value p κ N M e hp hκpos hNnd hMnd]


lemma rf_pfL (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n / m.gcd n).primeFactors = m.primeFactors ∪ n.primeFactors := by
  have hL : m * n / m.gcd n = Nat.lcm m n := by
    calc m * n / m.gcd n = m * (n / m.gcd n) := Nat.mul_div_assoc m (Nat.gcd_dvd_right m n)
      _ = Nat.lcm m n := Commons.Data.Nat.mul_div_gcd_eq_lcm m n
  rw [hL]
  ext p
  constructor
  · intro hp
    rcases (Nat.mem_primeFactors.mp hp) with ⟨hp0, hdvd, hl⟩
    rcases (hp0.dvd_lcm.mp hdvd) with h | h
    · exact Finset.mem_union.mpr (Or.inl (Nat.mem_primeFactors.mpr ⟨hp0, h, hm⟩))
    · exact Finset.mem_union.mpr (Or.inr (Nat.mem_primeFactors.mpr ⟨hp0, h, hn⟩))
  · intro hp
    rcases (Finset.mem_union.mp hp) with hp | hp
    · rcases (Nat.mem_primeFactors.mp hp) with ⟨hp0, hdvd, hmn⟩
      exact Nat.mem_primeFactors.mpr ⟨hp0, hp0.dvd_lcm.mpr (Or.inl hdvd), Nat.lcm_ne_zero hm hn⟩
    · rcases (Nat.mem_primeFactors.mp hp) with ⟨hp0, hdvd, hnn⟩
      exact Nat.mem_primeFactors.mpr ⟨hp0, hp0.dvd_lcm.mpr (Or.inr hdvd), Nat.lcm_ne_zero hm hn⟩

lemma rf_pf_m_eq (m n : ℕ) (hm : m ≠ 0) :
    m.primeFactors = (m / m.gcd n).primeFactors ∪ (m.gcd n).primeFactors := by
  have hg0 : 0 < m.gcd n := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
  have hM0 : 0 < m / m.gcd n := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.gcd_dvd_left m n)) hg0
  ext p
  constructor
  · intro hp
    rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hdvd, hmz⟩
    have hdvd' : p ∣ (m / m.gcd n) * (m.gcd n) := by
      have hm_eq : m = (m / m.gcd n) * (m.gcd n) := (Nat.div_mul_cancel (Nat.gcd_dvd_left m n)).symm
      rwa [hm_eq] at hdvd
    rcases (hpp.dvd_mul.mp hdvd') with h | h
    · exact Finset.mem_union.mpr (Or.inl (Nat.mem_primeFactors.mpr ⟨hpp, h, hM0.ne'⟩))
    · exact Finset.mem_union.mpr (Or.inr (Nat.mem_primeFactors.mpr ⟨hpp, h, hg0.ne'⟩))
  · intro hp
    rcases (Finset.mem_union.mp hp) with hp | hp
    · rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hdvd, hmn⟩
      have hm_eq : m = (m / m.gcd n) * (m.gcd n) := (Nat.div_mul_cancel (Nat.gcd_dvd_left m n)).symm
      refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, hm⟩
      rw [hm_eq]
      exact dvd_mul_of_dvd_left hdvd (m.gcd n)
    · rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hdvd, hmn⟩
      refine Nat.mem_primeFactors.mpr ⟨hpp, dvd_trans hdvd (Nat.gcd_dvd_left m n), hm⟩

lemma rf_pf_n_eq (m n : ℕ) (hn : n ≠ 0) :
    n.primeFactors = (n / m.gcd n).primeFactors ∪ (m.gcd n).primeFactors := by
  have hg0 : 0 < m.gcd n := Nat.gcd_pos_of_pos_right m (Nat.pos_of_ne_zero hn)
  have hN0 : 0 < n / m.gcd n := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.gcd_dvd_right m n)) hg0
  ext p
  constructor
  · intro hp
    rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hdvd, hnz⟩
    have hdvd' : p ∣ (n / m.gcd n) * (m.gcd n) := by
      have hn_eq : n = (n / m.gcd n) * (m.gcd n) := (Nat.div_mul_cancel (Nat.gcd_dvd_right m n)).symm
      rwa [hn_eq] at hdvd
    rcases (hpp.dvd_mul.mp hdvd') with h | h
    · exact Finset.mem_union.mpr (Or.inl (Nat.mem_primeFactors.mpr ⟨hpp, h, hN0.ne'⟩))
    · exact Finset.mem_union.mpr (Or.inr (Nat.mem_primeFactors.mpr ⟨hpp, h, hg0.ne'⟩))
  · intro hp
    rcases (Finset.mem_union.mp hp) with hp | hp
    · rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hdvd, hmn⟩
      have hn_eq : n = (n / m.gcd n) * (m.gcd n) := (Nat.div_mul_cancel (Nat.gcd_dvd_right m n)).symm
      refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, hn⟩
      rw [hn_eq]
      exact dvd_mul_of_dvd_left hdvd (m.gcd n)
    · rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hdvd, hmn⟩
      refine Nat.mem_primeFactors.mpr ⟨hpp, dvd_trans hdvd (Nat.gcd_dvd_right m n), hn⟩

lemma rf_pf_q_eq (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ((m / m.gcd n) * (n / m.gcd n)).primeFactors =
      (m / m.gcd n).primeFactors ∪ (n / m.gcd n).primeFactors := by
  have hg0 : 0 < m.gcd n := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
  have hM0 : 0 < m / m.gcd n := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.gcd_dvd_left m n)) hg0
  have hN0 : 0 < n / m.gcd n := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.gcd_dvd_right m n)) hg0
  ext p
  constructor
  · intro hp
    rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hdvd, hmn⟩
    rcases (hpp.dvd_mul.mp hdvd) with h | h
    · exact Finset.mem_union.mpr (Or.inl (Nat.mem_primeFactors.mpr ⟨hpp, h, hM0.ne'⟩))
    · exact Finset.mem_union.mpr (Or.inr (Nat.mem_primeFactors.mpr ⟨hpp, h, hN0.ne'⟩))
  · intro hp
    rcases (Finset.mem_union.mp hp) with hp | hp
    · rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hdvd, hmn⟩
      refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, mul_ne_zero hM0.ne' hN0.ne'⟩
      exact dvd_mul_of_dvd_left hdvd (n / m.gcd n)
    · rcases (Nat.mem_primeFactors.mp hp) with ⟨hpp, hdvd, hmn⟩
      refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, mul_ne_zero hM0.ne' hN0.ne'⟩
      exact dvd_mul_of_dvd_right hdvd (m / m.gcd n)

/-- primeFactors(L) = primeFactors(q) ∪ {p | g, p ∤ q} -/
lemma rf_pfL_eq_qF (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m * n / m.gcd n).primeFactors =
      Nat.primeFactors ((m / m.gcd n) * (n / m.gcd n)) ∪
      ((Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n))) := by
  classical
  have hg0 : 0 < m.gcd n := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
  have hM0 : 0 < m / m.gcd n := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.gcd_dvd_left m n)) hg0
  have hN0 : 0 < n / m.gcd n := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.gcd_dvd_right m n)) hg0
  calc
    (m * n / m.gcd n).primeFactors = m.primeFactors ∪ n.primeFactors := rf_pfL m n hm hn
    _ = (((m / m.gcd n).primeFactors ∪ (m.gcd n).primeFactors) ∪
        ((n / m.gcd n).primeFactors ∪ (m.gcd n).primeFactors)) := by
          rw [rf_pf_m_eq m n hm, rf_pf_n_eq m n hn]
    _ = (m / m.gcd n).primeFactors ∪ (n / m.gcd n).primeFactors ∪ (m.gcd n).primeFactors := by
          ext p; simp [Finset.mem_union, or_left_comm, or_assoc]; tauto
    _ = ((m / m.gcd n) * (n / m.gcd n)).primeFactors ∪ (m.gcd n).primeFactors := by
          rw [← rf_pf_q_eq m n hm hn]
    _ = ((m / m.gcd n) * (n / m.gcd n)).primeFactors ∪
        ((Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n))) := by
          ext p
          rw [Finset.mem_union, Finset.mem_union]
          constructor
          · intro h
            rcases h with hq | hg
            · exact Or.inl hq
            · by_cases hpq : p ∣ (m / m.gcd n) * (n / m.gcd n)
              · have hp' : p ∈ ((m / m.gcd n) * (n / m.gcd n)).primeFactors :=
                  Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hg).1, hpq, mul_ne_zero hM0.ne' hN0.ne'⟩
                exact Or.inl hp'
              · exact Or.inr (Finset.mem_filter.mpr ⟨hg, hpq⟩)
          · intro h
            rcases h with hq | hg
            · exact Or.inl hq
            · exact Or.inr ((Finset.mem_filter.mp hg).1)

/-- disjointness of the two parts of the prime support of L -/
lemma rf_disj_qF (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Disjoint (Nat.primeFactors ((m / m.gcd n) * (n / m.gcd n)))
      ((Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n))) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hq
  exact (Finset.mem_filter.mp hq).2 ((Nat.mem_primeFactors.mp hp).2.1)

/-- prime factors of K (K := ∏_{p ∈ F} p^(g.factorization p)) equal F -/
lemma rf_pfK_eq_F (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ((∏ p ∈ (Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n)),
        p ^ ((m.gcd n).factorization p)).primeFactors) =
      (Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n)) := by
  classical
  let F := (Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n))
  have hFdef : F = (Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n)) := rfl
  have hFpos : ∀ p ∈ F, p.Prime := by
    intro p hp
    exact (Nat.mem_primeFactors.mp ((Finset.mem_filter.mp hp).1)).1
  have hKf : ∀ p, ((∏ p ∈ F, p ^ ((m.gcd n).factorization p)).factorization) p =
      if p ∈ F then (m.gcd n).factorization p else 0 := by
    intro p
    exact Commons.Data.Nat.factorization_prod_prime_pow_apply F (fun q => (m.gcd n).factorization q) hFpos p
  have hKz : (∏ p ∈ F, p ^ ((m.gcd n).factorization p)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (hFpos p hp).ne_zero
  ext p
  constructor
  · intro hpK
    rcases (Nat.mem_primeFactors.mp hpK) with ⟨hpp, hdvd, hKnz⟩
    have hKfpos : 0 < (∏ p ∈ F, p ^ ((m.gcd n).factorization p)).factorization p := by
      have h1 : 1 ≤ (∏ p ∈ F, p ^ ((m.gcd n).factorization p)).factorization p :=
        (Nat.Prime.dvd_iff_one_le_factorization hpp hKz).mp hdvd
      omega
    rw [hKf p] at hKfpos
    by_cases hpFin : p ∈ F
    · rw [if_pos hpFin] at hKfpos
      exact hpFin
    · rw [if_neg hpFin] at hKfpos
      simp at hKfpos
  · intro hpF
    have hpF' : p ∈ F := by simpa [F] using hpF
    rcases (Finset.mem_filter.mp hpF') with ⟨hgm, hpq⟩
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hgm).1
    have hdvdg : p ∣ m.gcd n := (Nat.mem_primeFactors.mp hgm).2.1
    refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, hKz⟩
    have hpos : 0 < (m.gcd n).factorization p := by
      have h1 : 1 ≤ (m.gcd n).factorization p :=
        (Nat.Prime.dvd_iff_one_le_factorization hpp (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)).ne').mp hdvdg
      omega
    have h1 : 1 ≤ (∏ p ∈ F, p ^ ((m.gcd n).factorization p)).factorization p := by
      rw [hKf p, if_pos hpF']
      exact hpos
    exact (Nat.Prime.dvd_iff_one_le_factorization hpp hKz).mpr h1

/-- factorization of K at p ∈ F is g.factorization p -/
lemma rf_K_fact (m n p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hpF : p ∈ (Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n))) :
    ((∏ p ∈ (Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n)),
        p ^ ((m.gcd n).factorization p)).factorization) p = (m.gcd n).factorization p := by
  classical
  let F := (Nat.primeFactors (m.gcd n)).filter (fun p => ¬ p ∣ (m / m.gcd n) * (n / m.gcd n))
  have hFpos : ∀ q ∈ F, q.Prime := by
    intro q hq
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1
  have hKf : ((∏ q ∈ F, q ^ ((m.gcd n).factorization q)).factorization) p = if p ∈ F then (m.gcd n).factorization p else 0 :=
    Commons.Data.Nat.factorization_prod_prime_pow_apply F (fun q => (m.gcd n).factorization q) hFpos p
  have hpF' : p ∈ F := by simpa [F] using hpF
  rw [hKf, if_pos hpF']




/-- φ(p^k) − p^(k−1) = p^(k−1)·(p−2) -/
lemma rf_totient_pow_sub (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    (p ^ k).totient - p ^ (k - 1) = p ^ (k - 1) * (p - 2) := by
  rw [Nat.totient_prime_pow hp hk]
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : p - 1 = (p - 2) + 1 := by omega
  have hX : p ^ (k - 1) * (p - 1) = p ^ (k - 1) * (p - 2) + p ^ (k - 1) := by
    rw [hp1, Nat.mul_add, mul_one]
  calc
    p ^ (k - 1) * (p - 1) - p ^ (k - 1) =
        (p ^ (k - 1) * (p - 2) + p ^ (k - 1)) - p ^ (k - 1) := by rw [hX]
    _ = p ^ (k - 1) * (p - 2) := Nat.add_sub_cancel (p ^ (k - 1) * (p - 2)) (p ^ (k - 1))

/-- p | (e % L) iff p | e when p | L -/
lemma rf_dvd_mod_iff_dvd (p L e : ℕ) (hpL : p ∣ L) : p ∣ e % L ↔ p ∣ e := by
  have hme : e ≡ e % L [MOD L] := by
    change e % L = (e % L) % L
    exact (Nat.mod_mod e L).symm
  have hmp : e ≡ e % L [MOD p] := Nat.ModEq.of_dvd hpL hme
  exact (Nat.ModEq.dvd_iff hmp (dvd_refl p)).symm

theorem residue_fiber_formula (m n e : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let g : ℕ := m.gcd n
    let M : ℕ := m / g
    let N : ℕ := n / g
    let q : ℕ := M * N
    let L : ℕ := m * n / g
    let K : ℕ := ∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ q), p ^ (g.factorization p)
    let Phi : ℕ := ∏ p ∈ Nat.primeFactors q, (p ^ (g.factorization p)).totient
    let S : ℕ → ℕ := fun c => ∏ p ∈ Nat.primeFactors K,
        if p ∣ c then (p ^ (K.factorization p)).totient
        else p ^ (K.factorization p - 1) * (p - 2)
    (((Finset.product ((Finset.range m).filter (fun a : ℕ => a.gcd m = 1))
        ((Finset.range n).filter (fun b : ℕ => b.gcd n = 1))).filter
      (fun ab : ℕ × ℕ => ((ab.1 * N) % L = ((ab.2 * M + e) % L)))).card : ℕ) =
      if e.gcd q = 1 then Phi * S (e % L) else 0 := by
  classical
  dsimp
  set g := m.gcd n with hgdef
  set M := m / g with hMdef
  set N := n / g with hNdef
  set q := M * N with hqdef
  set L := m * n / g with hLdef
  set K := (∏ p ∈ (Nat.primeFactors g).filter (fun p => ¬ p ∣ q), p ^ (g.factorization p)) with hKdef
  set Phi := (∏ p ∈ Nat.primeFactors q, (p ^ (g.factorization p)).totient) with hPhidef
  set S := (fun c : ℕ => ∏ p ∈ Nat.primeFactors K,
        if p ∣ c then (p ^ (K.factorization p)).totient
        else p ^ (K.factorization p - 1) * (p - 2)) with hSdef
  -- context facts
  have hmn : m ≠ 0 := hm.ne'
  have hnn : n ≠ 0 := hn.ne'
  have hg0 : 0 < g := by rw [hgdef]; exact Nat.gcd_pos_of_pos_left n hm
  have hg_dvd_m : g ∣ m := by rw [hgdef]; exact Nat.gcd_dvd_left m n
  have hg_dvd_n : g ∣ n := by rw [hgdef]; exact Nat.gcd_dvd_right m n
  have hgm : g ≤ m := Nat.le_of_dvd hm hg_dvd_m
  have hgn : g ≤ n := Nat.le_of_dvd hn hg_dvd_n
  have hM0 : 0 < M := by dsimp [M]; exact Nat.div_pos hgm hg0
  have hN0 : 0 < N := by dsimp [N]; exact Nat.div_pos hgn hg0
  have hMne : M ≠ 0 := hM0.ne'
  have hNne : N ≠ 0 := hN0.ne'
  have hMdvdm : M ∣ m := by
    refine ⟨g, ?_⟩
    rw [hMdef]
    exact (Nat.div_mul_cancel hg_dvd_m).symm
  have hNdvdn : N ∣ n := by
    refine ⟨g, ?_⟩
    rw [hNdef]
    exact (Nat.div_mul_cancel hg_dvd_n).symm
  have hcopMN : M.Coprime N := by
    rw [hMdef, hNdef, hgdef]
    have hg0' : 0 < m.gcd n := by rwa [hgdef] at hg0
    exact Nat.coprime_div_gcd_div_gcd (m := m) (n := n) hg0'
  have hL_mN : L = m * N := by
    rw [hLdef, hNdef]
    exact Nat.mul_div_assoc m hg_dvd_n
  have hL_Mn : L = M * n := by
    rw [hLdef, hMdef]
    calc
      m * n / g = n * m / g := by rw [mul_comm m n]
      _ = n * (m / g) := Nat.mul_div_assoc n hg_dvd_m
      _ = (m / g) * n := by rw [mul_comm n (m / g)]
  have hL_lcm : L = Nat.lcm m n := by
    rw [hL_mN, hNdef, hgdef]
    exact Commons.Data.Nat.mul_div_gcd_eq_lcm m n
  have hL0 : 0 < L := by
    rw [hL_lcm]
    exact Nat.lcm_pos hm hn
  have hLne : L ≠ 0 := hL0.ne'
  have hq0 : 0 < q := by dsimp [q]; exact mul_pos hM0 hN0
  have hqne : q ≠ 0 := hq0.ne'
  have hg_dvd_L : g ∣ L := by
    rw [hL_lcm]
    exact dvd_trans hg_dvd_m (Nat.dvd_lcm_left m n)
  have hm_dvd_L : m ∣ L := by
    rw [hL_mN]
    exact dvd_mul_right m N
  have hn_dvd_L : n ∣ L := by
    rw [hL_Mn]
    exact dvd_mul_left n M
  have hpm : m.primeFactors ⊆ L.primeFactors := Nat.primeFactors_mono hm_dvd_L hLne
  have hpn : n.primeFactors ⊆ L.primeFactors := Nat.primeFactors_mono hn_dvd_L hLne
  have hLm : L ∣ m * N := by
    rw [hL_mN]
  have hLn : L ∣ n * M := by
    rw [hL_Mn]
    rw [mul_comm n M]
  -- main LHS is pairFiber
  change pairFiber m n N M L e =
    (if e.gcd q = 1 then Phi * S (e % L) else 0)
  by_cases hc : e.gcd q = 1
  · -- coprime case
    rw [if_pos hc]
    rw [pairFiber_eq_prod m n N M L e hm hn hL0 hLm hLn hpm hpn]
    let F := (Nat.primeFactors g).filter (fun p => ¬ p ∣ q)
    let piece : ℕ → ℕ := fun p =>
      pairFiber (p ^ m.factorization p) (p ^ n.factorization p) N M (p ^ L.factorization p) e
    have hpfL : L.primeFactors = Nat.primeFactors q ∪ F := by
      simpa [hgdef, hMdef, hNdef, hqdef, hLdef, F] using (rf_pfL_eq_qF m n hm.ne' hn.ne')
    have hdisj : Disjoint (Nat.primeFactors q) F := by
      simpa [hgdef, hMdef, hNdef, hqdef, F] using (rf_disj_qF m n hm.ne' hn.ne')
    have hpfK : Nat.primeFactors K = F := by
      have hK_rew : K = ∏ p ∈ F, p ^ (g.factorization p) := by
        rw [hKdef]
      rw [hK_rew]
      have h0 := rf_pfK_eq_F m n hm.ne' hn.ne'
      simpa [← hgdef, ← hMdef, ← hNdef, ← hqdef, F] using h0
    have hnotdiv_q : ∀ p : ℕ, p ∈ Nat.primeFactors q → ¬ p ∣ e := by
      intro p hp hpe
      have hpdq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
      have hpgcd : p ∣ e.gcd q := Nat.dvd_gcd hpe hpdq
      rw [hc] at hpgcd
      exact ((Nat.mem_primeFactors.mp hp).1).not_dvd_one hpgcd
    have hval_q : ∀ p ∈ Nat.primeFactors q, piece p = (p ^ g.factorization p).totient := by
      intro p hp
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpdq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
      have hdvd : p ∣ M ∨ p ∣ N := (hpp.dvd_mul.mp (by simpa [hqdef] using hpdq))
      have hne : ¬ p ∣ e := hnotdiv_q p hp
      rcases hdvd with hpM | hpN
      · have hv0 := rf_piece_qM m n e p hm hn hpp (by simpa [hMdef, hgdef] using hpM)
        have hv : piece p = if p ∣ e then 0 else (p ^ g.factorization p).totient := by
          simpa [piece, hMdef, hNdef, hLdef, hgdef] using hv0
        rwa [if_neg hne] at hv
      · have hv0 := rf_piece_qN m n e p hm hn hpp (by simpa [hNdef, hgdef] using hpN)
        have hv : piece p = if p ∣ e then 0 else (p ^ g.factorization p).totient := by
          simpa [piece, hMdef, hNdef, hLdef, hgdef] using hv0
        rwa [if_neg hne] at hv
    have hval_F : ∀ p ∈ F, piece p =
        (if p ∣ e % L then (p ^ (K.factorization p)).totient
         else p ^ (K.factorization p - 1) * (p - 2)) := by
      intro p hpF
      have hpp : p.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpF).1).1
      have hpdvg : p ∣ g := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpF).1).2.1
      have hpq : ¬ p ∣ q := (Finset.mem_filter.mp hpF).2
      have hpdL : p ∣ L := dvd_trans hpdvg hg_dvd_L
      have hKf : K.factorization p = g.factorization p := by
        have hraw := rf_K_fact m n p hm.ne' hn.ne' (by simpa [hgdef, hMdef, hNdef, hqdef, F] using hpF)
        rw [hKdef]
        rw [hgdef, hqdef, hMdef, hNdef]
        exact hraw
      have hpe_iff : p ∣ e % L ↔ p ∣ e := rf_dvd_mod_iff_dvd p L e hpdL
      have hgpos : 0 < g.factorization p := by
        have h1 : 1 ≤ g.factorization p :=
          (Nat.Prime.dvd_iff_one_le_factorization hpp hg0.ne').mp hpdvg
        omega
      have hv0 := rf_piece_K m n e p hm hn hpp (by simpa [hgdef] using hpdvg)
        (by simpa [hqdef, hMdef, hNdef, hgdef] using hpq)
      have hv : piece p = if p ∣ e then (p ^ g.factorization p).totient
            else (p ^ g.factorization p).totient - p ^ (g.factorization p - 1) := by
        simpa [piece, hMdef, hNdef, hLdef, hgdef] using hv0
      by_cases hpe : p ∣ e
      · have hpeL : p ∣ e % L := hpe_iff.mpr hpe
        rw [if_pos hpeL]
        rw [if_pos hpe] at hv
        rw [hv]
        rw [hKf]
      · have hneL : ¬ p ∣ e % L := by
          intro h
          exact hpe (hpe_iff.mp h)
        rw [if_neg hneL]
        rw [if_neg hpe] at hv
        rw [hv]
        rw [hKf]
        rw [rf_totient_pow_sub p (g.factorization p) hpp hgpos]
    calc
      (∏ p ∈ L.primeFactors, piece p) = ∏ p ∈ (Nat.primeFactors q ∪ F), piece p := by
        rw [hpfL]
      _ = (∏ p ∈ Nat.primeFactors q, piece p) * (∏ p ∈ F, piece p) := by
        rw [Finset.prod_union hdisj]
      _ = Phi * S (e % L) := by
        calc
          (∏ p ∈ Nat.primeFactors q, piece p) * (∏ p ∈ F, piece p)
              = (∏ p ∈ Nat.primeFactors q, (p ^ g.factorization p).totient) *
                (∏ p ∈ F, (if p ∣ e % L then (p ^ (K.factorization p)).totient
                           else p ^ (K.factorization p - 1) * (p - 2))) := by
                congr 1
                · exact Finset.prod_congr rfl (fun p hp => hval_q p hp)
                · exact Finset.prod_congr rfl (fun p hp => hval_F p hp)
          _ = Phi * S (e % L) := by
            have hA : (∏ p ∈ Nat.primeFactors q, (p ^ g.factorization p).totient) = Phi := by
              rw [hPhidef]
            have hB : (∏ p ∈ F,
                (if p ∣ e % L then (p ^ (K.factorization p)).totient
                 else p ^ (K.factorization p - 1) * (p - 2))) = S (e % L) := by
              rw [hSdef]
              rw [hpfK]
            rw [← hA, ← hB]
  · -- non-coprime case: LHS = 0
    rw [if_neg hc]
    have hnot : ¬ e.gcd ((m / m.gcd n) * (n / m.gcd n)) = 1 := by
      intro h1
      exact hc (by simpa [hqdef, hMdef, hNdef, hgdef] using h1)
    rw [pairFiber_zero_of_not_coprime_q m n e hm hn hnot]

end Commons.NumberTheory.DuffinSchaeffer