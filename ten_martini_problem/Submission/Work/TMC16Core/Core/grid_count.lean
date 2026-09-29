import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Trig.grid_sep

/-!
# Counting the grid points `2x + k·(p/q)` that come close to an integer

`grid_count` is the counting estimate used in AJ §9: for `q ≥ 1`, `p : ℤ` coprime to `q`,
`x : ℝ` and `γ > 0`, at most `2γq + 2` of the numbers
`2x + k·(p/q)`, `k = 1, …, q`, lie within distance `γ` of an integer.

The proof does not need the full residue bijection `k ↦ k·p mod q`; the two facts used are

* **separation**: for distinct `k, l ∈ {1,…,q}` the difference of the two grid points is
  `(k-l)·p/q` with `0 < |k-l| < q`, hence not an integer because `p` is coprime to `q`;
  therefore `nn (w k - w l) ≥ 1/q` (`nn_grid_pair_sep`), and
* **the lattice count**: if each `t_k := w_k - round w_k` lies in `(-γ, γ)` and the `t_k`
  are pairwise `1/q`-separated, then `t ↦ ⌊q·t⌋` is an injection of the set of such `k`
  into the integer interval `[⌊-qγ⌋, ⌊qγ⌋]`, which has at most `2γq + 2` elements
  (`card_le_of_mem_Ioo_sep`).
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core.Basic

/-! ## Auxiliary arithmetic lemmas -/

/-- The absolute value of the real image of an integer is its `natAbs`. -/
private lemma abs_intCast_eq_natAbs (z : ℤ) : |((z : ℤ) : ℝ)| = ((z.natAbs : ℕ) : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp

/-- **Key lower bound.**  If the integer `N` is not divisible by `q > 0`, then
`N/q` is at distance at least `1/q` from every integer. -/
private lemma nn_int_div_nat_ge (N : ℤ) {q : ℕ} (hq : 0 < q) (hndvd : ¬ (q:ℤ) ∣ N) :
    1/(q:ℝ) ≤ nn ((N:ℝ)/(q:ℝ)) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  rw [nn]
  set m : ℤ := round ((N:ℝ)/(q:ℝ)) with hm
  have hz : N - m * (q:ℤ) ≠ 0 := by
    intro h
    apply hndvd
    exact ⟨m, by linarith⟩
  have hdiff : (N:ℝ)/(q:ℝ) - (m:ℝ) = (((N - m*(q:ℤ)):ℤ):ℝ) / (q:ℝ) := by
    push_cast; field_simp
  rw [hdiff, abs_div, abs_of_pos hqR, abs_intCast_eq_natAbs]
  have hge : (1:ℝ) ≤ ((N - m*(q:ℤ)).natAbs : ℝ) := by
    have : 1 ≤ (N - m*(q:ℤ)).natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hz)
    exact_mod_cast this
  exact div_le_div_of_nonneg_right hge hqR.le

/-- Euclid's lemma over `ℤ`, coprime form: if `p` is coprime to `q` and `q ∣ d * p`,
then `q ∣ d`. -/
private lemma dvd_of_dvd_mul_of_coprime {p d : ℤ} {q : ℕ} (hcop : Nat.Coprime p.natAbs q)
    (h : (q:ℤ) ∣ d * p) : (q:ℤ) ∣ d := by
  have hgcd : Int.gcd p (q:ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact hcop.gcd_eq_one
  have hbez : p * p.gcdA (q:ℤ) + (q:ℤ) * p.gcdB (q:ℤ) = 1 := by
    have hh := Int.gcd_eq_gcd_ab p (q:ℤ)
    rw [hgcd] at hh
    norm_num at hh
    exact hh.symm
  have hd : d = (d * p) * p.gcdA (q:ℤ) + (d * p.gcdB (q:ℤ)) * (q:ℤ) := by
    calc d = d * (p * p.gcdA (q:ℤ) + (q:ℤ) * p.gcdB (q:ℤ)) := by rw [hbez, mul_one]
      _ = (d * p) * p.gcdA (q:ℤ) + (d * p.gcdB (q:ℤ)) * (q:ℤ) := by ring
  rw [hd]
  exact dvd_add (h.mul_right _) (dvd_mul_left (q:ℤ) (d * p.gcdB (q:ℤ)))

/-- With `p` coprime to `q` and `0 < |d| < q`, the product `d * p` is not divisible
by `q`. -/
private lemma not_dvd_mul {p : ℤ} {q : ℕ} (hcop : Nat.Coprime p.natAbs q)
    {d : ℤ} (hd0 : d ≠ 0) (hdl : d.natAbs < q) : ¬ (q:ℤ) ∣ d * p := by
  intro h
  have hdvd : (q:ℤ) ∣ d := dvd_of_dvd_mul_of_coprime hcop h
  obtain ⟨t, ht⟩ := hdvd
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
    exact hd0 ht
  have hnat : d.natAbs = q * t.natAbs := by
    rw [ht, Int.natAbs_mul, Int.natAbs_natCast]
  have h1 : 1 ≤ t.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ht0)
  have hqle : q ≤ d.natAbs := by
    rw [hnat]
    calc q = q * 1 := by ring
      _ ≤ q * t.natAbs := Nat.mul_le_mul_left q h1
  omega

/-! ## Pairwise separation of the grid -/

/-- **Pairwise separation of the `nn`-grid.**  For `q ≥ 1`, `p : ℤ` coprime to `q`, `x : ℝ`
and distinct `k, l ∈ {1, …, q}`, the difference of the two grid points is the rational
`(k-l)·p/q` with denominator `q` in lowest terms, so `nn` of that difference is `≥ 1/q`. -/
lemma nn_grid_pair_sep {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q)
    (x : ℝ) {k l : ℕ} (hk : k ∈ Finset.Icc 1 q) (hl : l ∈ Finset.Icc 1 q) (hkl : k ≠ l) :
    1 / (q:ℝ) ≤ nn
      ((2 * x + (k:ℝ) * ((p:ℝ)/(q:ℝ))) - (2 * x + (l:ℝ) * ((p:ℝ)/(q:ℝ)))) := by
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkq : k ≤ q := (Finset.mem_Icc.mp hk).2
  have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
  have hlq : l ≤ q := (Finset.mem_Icc.mp hl).2
  have hd0 : ((k:ℤ) - (l:ℤ)) ≠ 0 := by
    intro h
    apply hkl
    have h' : (k:ℤ) = (l:ℤ) := sub_eq_zero.mp h
    exact_mod_cast h'
  have hdl : ((k:ℤ) - (l:ℤ)).natAbs < q := by omega
  have hndvd : ¬ (q:ℤ) ∣ ((k:ℤ) - (l:ℤ)) * p := not_dvd_mul hcop hd0 hdl
  have hdiff : (2 * x + (k:ℝ) * ((p:ℝ)/(q:ℝ))) - (2 * x + (l:ℝ) * ((p:ℝ)/(q:ℝ)))
      = ((((k:ℤ) - (l:ℤ)) * p : ℤ) : ℝ) / (q:ℝ) := by
    push_cast; field_simp; ring
  rw [hdiff]
  exact nn_int_div_nat_ge _ hq hndvd

/-! ## Counting separated reals in an interval -/

/-- **Counting separated reals near the integers.**  If `T` is a finite set of reals, each
lying strictly inside `(-γ, γ)` with `γ > 0`, and whose elements are pairwise at distance at
least `1/q` (`q ≥ 1`), then `T` has at most `2qγ + 2` elements. -/
lemma card_le_of_mem_Ioo_sep {q : ℕ} (hq : 0 < q) {γ : ℝ} (hγ : 0 < γ) (T : Finset ℝ)
    (hmem : ∀ t ∈ T, -γ < t ∧ t < γ)
    (hsep : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → 1/(q:ℝ) ≤ |s - t|) :
    (T.card : ℝ) ≤ 2 * (q:ℝ) * γ + 2 := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  set lo : ℤ := ⌊-((q:ℝ) * γ)⌋ with hlo
  set hi : ℤ := ⌊(q:ℝ) * γ⌋ with hhi
  have hlo_le_hi : lo ≤ hi := by
    rw [hlo, hhi]
    exact Int.floor_le_floor (by nlinarith)
  have hmap : ∀ t ∈ T, ⌊(q:ℝ) * t⌋ ∈ Finset.Icc lo hi := by
    intro t ht
    obtain ⟨h1, h2⟩ := hmem t ht
    rw [Finset.mem_Icc, hlo, hhi]
    exact ⟨Int.floor_le_floor (by nlinarith), Int.floor_le_floor (by nlinarith)⟩
  have hinj : Set.InjOn (fun t : ℝ => ⌊(q:ℝ) * t⌋) ↑T := by
    intro s hs t ht hst
    by_contra hne
    have habs : (q:ℝ) * |s - t| = |(q:ℝ) * s - (q:ℝ) * t| := by
      calc (q:ℝ) * |s - t| = |(q:ℝ)| * |s - t| := by rw [abs_of_pos hqR]
        _ = |(q:ℝ) * (s - t)| := by rw [abs_mul]
        _ = |(q:ℝ) * s - (q:ℝ) * t| := by rw [mul_sub]
    have h1 : (1:ℝ) ≤ |(q:ℝ) * s - (q:ℝ) * t| := by
      have h2 := hsep s hs t ht hne
      have hqinv : (q:ℝ) * (1/(q:ℝ)) = 1 := by field_simp
      calc (1:ℝ) = (q:ℝ) * (1/(q:ℝ)) := hqinv.symm
        _ ≤ (q:ℝ) * |s - t| := mul_le_mul_of_nonneg_left h2 hqR.le
        _ = |(q:ℝ) * s - (q:ℝ) * t| := habs
    have h3 : |(q:ℝ) * s - (q:ℝ) * t| < 1 := by
      have hs1 : ((⌊(q:ℝ) * s⌋ : ℤ) : ℝ) ≤ (q:ℝ) * s := Int.floor_le _
      have hs2 : (q:ℝ) * s < ((⌊(q:ℝ) * s⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
      have ht1 : ((⌊(q:ℝ) * t⌋ : ℤ) : ℝ) ≤ (q:ℝ) * t := Int.floor_le _
      have ht2 : (q:ℝ) * t < ((⌊(q:ℝ) * t⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
      have hst' : ⌊(q:ℝ) * s⌋ = ⌊(q:ℝ) * t⌋ := hst
      rw [hst'] at hs1 hs2
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    linarith
  have hcard := Finset.card_le_card_of_injOn (fun t : ℝ => ⌊(q:ℝ) * t⌋) hmap hinj
  rw [Int.card_Icc] at hcard
  have hm_nonneg : 0 ≤ hi + 1 - lo := by omega
  have hcardZ : (T.card : ℤ) ≤ hi + 1 - lo := by
    have h := hcard
    have h' : ((T.card : ℕ) : ℤ) ≤ (((hi + 1 - lo).toNat : ℕ) : ℤ) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg hm_nonneg] at h'
  have hR : (T.card : ℝ) ≤ (hi : ℝ) + 1 - (lo : ℝ) := by exact_mod_cast hcardZ
  have hhi : (hi : ℝ) ≤ (q:ℝ) * γ := by rw [hhi]; exact Int.floor_le _
  have hlo' : -((q:ℝ) * γ) < (lo : ℝ) + 1 := by rw [hlo]; exact Int.lt_floor_add_one _
  linarith

/-! ## The main counting theorem -/

/-- **Counting grid points near integers.**

Let `q ≥ 1`, `p : ℤ` coprime to `q`, `x : ℝ`.  Since `k ↦ k * p mod q` is a bijection of the
residues modulo `q`, the `q` numbers `2x + k * (p/q)`, `k ∈ {1,…,q}`, are exactly the `q`
equally spaced grid points `2x + j/q` (`j = 0,…,q-1`); in particular any two of them differ by
a multiple of `1/q`, so those within distance `γ` of an integer form an arc of length `2γ`
containing `(1/q)`-separated points.  Hence their number is at most `2 γ q + 2`.  (The `+2`
covers the two sides of the integer.) -/
theorem grid_count {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (x : ℝ)
    (γ : ℝ) (hγ : 0 < γ) :
    ((Finset.Icc 1 q).filter
        (fun k : ℕ => Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < γ)).card
      ≤ 2 * (q : ℝ) * γ + 2 := by
  classical
  let A : ℕ → ℝ := fun k => 2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))
  let S : Finset ℕ := (Finset.Icc 1 q).filter (fun k : ℕ => Basic.nn (A k) < γ)
  let t : ℕ → ℝ := fun k => A k - ((round (A k) : ℤ) : ℝ)
  show (S.card : ℝ) ≤ 2 * (q : ℝ) * γ + 2
  have hS : ∀ k, k ∈ S ↔ k ∈ Finset.Icc 1 q ∧ Basic.nn (A k) < γ := by
    intro k
    change k ∈ (Finset.Icc 1 q).filter (fun k : ℕ => Basic.nn (A k) < γ) ↔ _
    rw [Finset.mem_filter]
  have hAeq : ∀ k, A k = 2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)) := fun k => rfl
  have hteq : ∀ k, t k = A k - ((round (A k) : ℤ) : ℝ) := fun k => rfl
  have hnnt : ∀ k, |t k| = Basic.nn (A k) := fun k => rfl
  have hmem : ∀ k ∈ S, -γ < t k ∧ t k < γ := by
    intro k hk
    have hlt : Basic.nn (A k) < γ := ((hS k).mp hk).2
    exact abs_lt.mp ((hnnt k).symm ▸ hlt)
  have hsep : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → 1/(q:ℝ) ≤ |t k - t l| := by
    intro k hk l hl hkl
    obtain ⟨hkI, -⟩ := (hS k).mp hk
    obtain ⟨hlI, -⟩ := (hS l).mp hl
    have hpair : 1/(q:ℝ) ≤ nn (A k - A l) := by
      have h := nn_grid_pair_sep hq hcop x hkI hlI hkl
      simpa only [hAeq] using h
    have hsplit : A k - A l = (t k - t l) + (((round (A k) - round (A l)) : ℤ) : ℝ) := by
      rw [hteq k, hteq l]; push_cast; ring
    have hnn : nn (A k - A l) = nn (t k - t l) := by rw [hsplit, nn_add_intCast]
    have hle : nn (t k - t l) ≤ |t k - t l| := nn_le_abs _
    linarith
  have hinj : Set.InjOn t ↑S := by
    intro k hk l hl heq
    by_contra hne
    have h := hsep k hk l hl hne
    rw [heq, sub_self, abs_zero] at h
    have : (0:ℝ) < 1/(q:ℝ) := by positivity
    linarith
  have hcard : (S.image t).card = S.card := Finset.card_image_of_injOn hinj
  have hmain : ((S.image t).card : ℝ) ≤ 2 * (q:ℝ) * γ + 2 := by
    apply card_le_of_mem_Ioo_sep hq hγ
    · intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨k, hk, rfl⟩ := hs
      exact hmem k hk
    · intro s hs s' hs' hne
      rw [Finset.mem_image] at hs hs'
      obtain ⟨k, hk, rfl⟩ := hs
      obtain ⟨l, hl, rfl⟩ := hs'
      exact hsep k hk l hl (fun h => hne (by rw [h]))
  rw [hcard] at hmain
  exact hmain

end Work.TMC16Core.Core
