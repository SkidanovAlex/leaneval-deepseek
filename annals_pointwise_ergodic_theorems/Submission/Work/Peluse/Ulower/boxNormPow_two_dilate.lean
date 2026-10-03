/-
# The dilation identity for the level-two box-norm power

Peluse's level-two box-norm power with the *dilated* direction set `c[D] = {c, 2c, …, Dc}` and
window `[-L,L]` decomposes, modulo the residue classes of `|c|`, into the box-norm powers with the
plain direction set `[D] = {1, 2, …, D}` of the `|c|` dilates

`g_r z = F (c * z + r)`,  `r = 0, 1, …, |c| - 1`,

each taken over the window `[-L/|c| - 1, L/|c| + 1]`:

`‖F‖^{2^2}_{□²_{c[D]}([-L,L])}
   = |[-L,L]|⁻¹ · ∑_{r < |c|} |[-L/|c|-1, L/|c|+1]| · ‖g_r‖^{2^2}_{□²_{[D]}([-L/|c|-1, L/|c|+1])}`.

## Proof

Expand both sides with the sum-of-squares formula for the level-two box-norm power
(`Work.Peluse.BoxNormDilation.boxNormPow_two_eq`),

`‖f‖^{2^2}_{□²_Q(S)} = |S|⁻¹ |Q|⁻⁴ ∑_{a,b ∈ Q} ∑_x ‖∑_{k ∈ Q} f(x+a+k)·conj(f(x+b+k))‖²`,

and observe that in the inner sum `a, b, k` all lie in `c[D]`, so writing `a = c a'`, `b = c b'`,
`k = c k'` and `x = c z + r` with `r ∈ {0, …, |c|-1}` turns the summand into

`‖∑_{k' ∈ [D]} g_r(z + a' + k')·conj(g_r(z + b' + k'))‖²`.

Two bookkeeping facts make this exact:

* `∑_{a ∈ c[D]} f a = ∑_{a' ∈ [D]} f (c a')` (the map `a' ↦ c a'` is a bijection `[D] → c[D]`,
  consequence of `c ≠ 0`), and `|c[D]| = D = |[D]|`, so the two `|Q|⁻⁴` normalisations coincide;
* the residue classes `x = c z + r` (`r < |c|`) partition `ℤ`
  (`Work.Peluse.Ulower.tsum_mod_split_aux`), which converts `∑_x` into `∑_{r<|c|} ∑_z`; that step uses
  that the summand vanishes off the finite window, which is where `SupportIn F L` enters.

The extra factor `|[-L/|c|-1, L/|c|+1]|` in the statement of the theorem is exactly the reciprocal
of the normalisation `|S'|⁻¹` produced by `boxNormPow_two_eq` for each dilate, so it cancels.

## Main result

* `Work.Peluse.Ulower.boxNormPow_two_dilate`
-/
import Mathlib
import Submission.Work.Peluse.BoxNormDilation.boxNormPow_two_eq

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Elementary facts about `symIcc` and `arithIcc` -/

/-- Membership in the symmetric interval, in terms of `Int.natAbs`. -/
private theorem mem_symIcc {x : ℤ} {L : ℕ} : x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (x.natAbs : ℤ) ≤ (L : ℤ) := by
      rw [Int.natCast_natAbs]
      exact abs_le.mpr ⟨h1, h2⟩
    exact_mod_cast h3
  · intro h
    have h3 : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at h3
    exact abs_le.mp h3

/-- The cardinality of the symmetric interval `[-L,L]`. -/
theorem card_symIcc (L : ℕ) : (symIcc L).card = 2 * L + 1 := by
  rw [symIcc, Int.card_Icc]
  have h1 : (L : ℤ) + 1 - (-(L : ℤ)) = (2 * L + 1 : ℕ) := by push_cast; ring
  rw [h1]
  exact Int.toNat_natCast (2 * L + 1)

/-- The cardinality of the arithmetic progression `c[D]`, for `c ≠ 0`. -/
private theorem card_arithIcc {c : ℤ} (hc : c ≠ 0) (D : ℕ) : (arithIcc c D).card = D := by
  rw [arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
    exact_mod_cast h

/-- `[D] ⊆ [-D,D]`. -/
private theorem subset_symIcc_of_arithIcc_one {D : ℕ} : arithIcc 1 D ⊆ symIcc D := by
  intro k hk
  rw [arithIcc] at hk
  rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
  rw [mem_symIcc]
  have h := (Finset.mem_Icc.mp hn).2
  simpa using h

/-- The dilation `c[D]` of `[D]` written as an image. -/
private theorem arithIcc_eq_image (c : ℤ) (D : ℕ) :
    arithIcc c D = (arithIcc 1 D).image (fun x : ℤ => c * x) := by
  rw [arithIcc, arithIcc, Finset.image_image]
  exact Finset.image_congr (fun n _ => by simp)

/-- Sums over the dilated direction set `c[D]` reindex to sums over `[D]`. -/
private theorem sum_arithIcc_c {α : Type*} [AddCommMonoid α] {c : ℤ} (hc : c ≠ 0) (D : ℕ)
    (f : ℤ → α) :
    ∑ a ∈ arithIcc c D, f a = ∑ a ∈ arithIcc 1 D, f (c * a) := by
  rw [arithIcc_eq_image]
  exact Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hc hab)

/-! ## Splitting a finitely supported sum over `ℤ` into residue classes modulo `c` -/

variable {c : ℤ} {N : ℕ} {v : ℤ → ℝ}

/-- The `x`-component of the Euclidean division by `c`, as a natural number in `[0,|c|)`. -/
private def rep (c : ℤ) (x : ℤ) : ℕ := (x % c).toNat

private lemma rep_cast (hc : c ≠ 0) (x : ℤ) : ((rep c x : ℕ) : ℤ) = x % c :=
  Int.toNat_of_nonneg (Int.emod_nonneg x hc)

private lemma rep_lt (hc : c ≠ 0) (x : ℤ) : rep c x < c.natAbs := by
  have h1 : (x % c) < |c| := Int.emod_lt_abs x hc
  have h2 : ((rep c x : ℕ) : ℤ) < ((c.natAbs : ℕ) : ℤ) := by
    rw [rep_cast hc, Int.natCast_natAbs]; exact h1
  exact_mod_cast h2

/-- **The residue classes modulo `c` split a finitely supported sum over `ℤ`.** -/
private theorem tsum_mod_split_aux (hc : c ≠ 0) (hv : ∀ x : ℤ, N < x.natAbs → v x = 0) :
    ∑' x : ℤ, v x = ∑ r ∈ Finset.range c.natAbs, ∑' z : ℤ, v (c * z + (r : ℤ)) := by
  have hm : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have hL : ∑' x : ℤ, v x = ∑ x ∈ symIcc N, v x := by
    rw [tsum_eq_sum (s := symIcc N)]
    intro x hx
    exact hv x (Nat.lt_of_not_le (fun h => hx (mem_symIcc.mpr h)))
  have hR : ∀ r ∈ Finset.range c.natAbs,
      ∑' z : ℤ, v (c * z + (r : ℤ)) = ∑ z ∈ symIcc N, v (c * z + (r : ℤ)) := by
    intro r hr
    rw [tsum_eq_sum (s := symIcc N)]
    intro z hz
    apply hv
    have hrm : r < c.natAbs := Finset.mem_range.mp hr
    have hzN : N < z.natAbs := Nat.lt_of_not_le (fun h => hz (mem_symIcc.mpr h))
    have h1 : c.natAbs * z.natAbs ≤ (c * z + (r : ℤ)).natAbs + r := by
      have h := Int.natAbs_add_le (c * z + (r : ℤ)) (-(r : ℤ))
      rw [Int.natAbs_neg, add_neg_cancel_right] at h
      rw [Int.natAbs_mul] at h
      simpa using h
    have h2 : N + r + 1 ≤ c.natAbs * z.natAbs := by
      have hz1 : N + 1 ≤ z.natAbs := by omega
      have h3 : c.natAbs * (N + 1) ≤ c.natAbs * z.natAbs := Nat.mul_le_mul_left _ hz1
      have h4 : N + r + 1 ≤ c.natAbs * (N + 1) := by
        have h7 : N ≤ c.natAbs * N := Nat.le_mul_of_pos_left N hm
        have h8 : c.natAbs * (N + 1) = c.natAbs * N + c.natAbs := by ring
        omega
      omega
    omega
  have h3 : (∑ x ∈ symIcc N, v x)
      = ∑ r ∈ Finset.range c.natAbs, ∑ z ∈ symIcc N, v (c * z + (r : ℤ)) := by
    let T : Finset (ℕ × ℤ) := Finset.range c.natAbs ×ˢ symIcc N
    let ps : ℕ × ℤ → ℤ := fun p => c * p.2 + (p.1 : ℤ)
    have hinj : Set.InjOn ps ↑T := by
      intro p hp q hq hpq
      have hp1 : p.1 < c.natAbs := Finset.mem_range.mp (Finset.mem_product.mp hp).1
      have hq1 : q.1 < c.natAbs := Finset.mem_range.mp (Finset.mem_product.mp hq).1
      have hkey : c * (p.2 - q.2) = (q.1 : ℤ) - (p.1 : ℤ) := by
        have h := hpq
        simp only [ps] at h
        linear_combination h
      have h2p : (p.1 : ℤ) < (c.natAbs : ℤ) := by exact_mod_cast hp1
      have h2q : (q.1 : ℤ) < (c.natAbs : ℤ) := by exact_mod_cast hq1
      have h0p : (0 : ℤ) ≤ (p.1 : ℤ) := by positivity
      have h0q : (0 : ℤ) ≤ (q.1 : ℤ) := by positivity
      have habs : (c.natAbs : ℤ) * |p.2 - q.2| = |(q.1 : ℤ) - (p.1 : ℤ)| := by
        rw [← hkey, abs_mul, Int.natCast_natAbs]
      have habslt : |(q.1 : ℤ) - (p.1 : ℤ)| < (c.natAbs : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      have hpos : (0 : ℤ) < (c.natAbs : ℤ) := by exact_mod_cast hm
      have hlt1 : |p.2 - q.2| < 1 := by
        have hlt : |p.2 - q.2| * (c.natAbs : ℤ) < 1 * (c.natAbs : ℤ) := by
          calc |p.2 - q.2| * (c.natAbs : ℤ) = (c.natAbs : ℤ) * |p.2 - q.2| := by ring
            _ = |(q.1 : ℤ) - (p.1 : ℤ)| := habs
            _ < (c.natAbs : ℤ) := habslt
            _ = 1 * (c.natAbs : ℤ) := by ring
        exact lt_of_mul_lt_mul_right hlt (le_of_lt hpos)
      have hp2 : p.2 = q.2 := by
        have hb := abs_lt.mp hlt1
        omega
      have hp1' : p.1 = q.1 := by
        have h : (p.1 : ℤ) = (q.1 : ℤ) := by
          have h' := hpq
          simp only [ps] at h'
          rw [hp2] at h'
          omega
        exact_mod_cast h
      exact Prod.ext hp1' hp2
    have hsurj : ∀ x ∈ symIcc N, ∃ p ∈ T, ps p = x := by
      intro x hxN
      have hxN' : x.natAbs ≤ N := mem_symIcc.mp hxN
      refine ⟨(rep c x, x / c), ?_, ?_⟩
      · show (rep c x, x / c) ∈ T
        simp only [T, Finset.mem_product, Finset.mem_range]
        refine ⟨rep_lt hc x, ?_⟩
        rw [mem_symIcc]
        have htri : (x - x % c).natAbs ≤ x.natAbs + rep c x := by
          have h := Int.natAbs_sub_le x (x % c)
          have h2 : (x % c).natAbs = rep c x := by
            rw [← rep_cast hc x]; simp
          omega
        have hbound : c.natAbs * (x / c).natAbs ≤ N + rep c x := by
          have hcz : c * (x / c) = x - x % c := by
            have h := Int.mul_ediv_add_emod x c
            linarith
          have hcast : ((x - x % c).natAbs : ℤ) ≤ (N : ℤ) + (rep c x : ℕ) := by
            have hN : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hxN'
            have htr2 : ((x - x % c).natAbs : ℤ) ≤ (x.natAbs : ℤ) + (rep c x : ℕ) := by
              exact_mod_cast htri
            linarith
          have hmul : ((c * (x / c)).natAbs : ℤ) ≤ (N : ℤ) + (rep c x : ℕ) := by
            rw [hcz]; exact hcast
          have hmul2 : ((c * (x / c)).natAbs : ℤ)
              = (c.natAbs : ℤ) * ((x / c).natAbs : ℤ) := by
            rw [Int.natAbs_mul]; push_cast; ring
          have hmul3 : (c.natAbs : ℤ) * ((x / c).natAbs : ℤ)
              ≤ (N : ℤ) + (rep c x : ℕ) := by
            rw [← hmul2]; exact hmul
          have hz : (((c.natAbs * (x / c).natAbs : ℕ)) : ℤ) ≤ ((N + rep c x : ℕ) : ℤ) := by
            have hL : (((c.natAbs * (x / c).natAbs : ℕ)) : ℤ)
                = (c.natAbs : ℤ) * ((x / c).natAbs : ℤ) := by rw [Nat.cast_mul]
            have hR : ((N + rep c x : ℕ) : ℤ) = (N : ℤ) + (rep c x : ℕ) := by rw [Nat.cast_add]
            rw [hL, hR]; exact hmul3
          exact Int.ofNat_le.mp hz
        by_contra hcon
        have hcon' : N < (x / c).natAbs := Nat.lt_of_not_le hcon
        have hz1 : N + 1 ≤ (x / c).natAbs := by omega
        have h5 : c.natAbs * (N + 1) ≤ c.natAbs * (x / c).natAbs := Nat.mul_le_mul_left _ hz1
        have h6 : N + c.natAbs ≤ c.natAbs * (N + 1) := by
          have h7 : N ≤ c.natAbs * N := Nat.le_mul_of_pos_left N hm
          have h8 : c.natAbs * (N + 1) = c.natAbs * N + c.natAbs := by ring
          omega
        have hrep : rep c x + 1 ≤ c.natAbs := by
          have := rep_lt hc x
          omega
        omega
      · show c * (x / c) + ((rep c x : ℕ) : ℤ) = x
        rw [rep_cast hc x]
        exact Int.mul_ediv_add_emod x c
    have hsub : symIcc N ⊆ T.image ps := by
      intro x hx
      obtain ⟨p, hp, hpv⟩ := hsurj x hx
      exact Finset.mem_image.mpr ⟨p, hp, hpv⟩
    have hvan : ∀ x ∈ T.image ps, x ∉ symIcc N → v x = 0 := by
      intro x _ hx
      exact hv x (Nat.lt_of_not_le (fun h => hx (mem_symIcc.mpr h)))
    have h4 : (∑ x ∈ T.image ps, v x) = ∑ p ∈ T, v (ps p) := Finset.sum_image hinj
    have h5 : (∑ x ∈ symIcc N, v x) = ∑ x ∈ T.image ps, v x := Finset.sum_subset hsub hvan
    have h6 : (∑ p ∈ T, v (ps p))
        = ∑ r ∈ Finset.range c.natAbs, ∑ z ∈ symIcc N, v (c * z + (r : ℤ)) := by
      show (∑ p ∈ Finset.range c.natAbs ×ˢ symIcc N, v (c * p.2 + (p.1 : ℤ))) = _
      rw [Finset.sum_product]
    rw [h5, h4, h6]
  rw [hL, h3]
  exact Finset.sum_congr rfl (fun r hr => (hR r hr).symm)

/-! ## The dilates and the summand of the box sum -/

/-- The summand of the level-two box-norm power of the dilate `g_r` — with the direction set
written in the plain form `[D]` and the argument kept in the "undilated" variable `x`. -/
private def psi (c : ℤ) (D : ℕ) (F : ℤ → ℂ) (a b : ℤ) (x : ℤ) : ℝ :=
  ‖∑ k ∈ arithIcc 1 D, F (x + c * a + c * k) * star (F (x + c * b + c * k))‖ ^ 2

/-! ## The dilation identity -/

theorem boxNormPow_two_dilate {c : ℤ} (hc : c ≠ 0) {D L : ℕ} (hD : 1 ≤ D) (F : ℤ → ℂ)
    (hFs : Work.Peluse.SupportIn F L) :
    Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc c D) (Work.Peluse.symIcc L) F
      = ((Work.Peluse.symIcc L).card : ℝ)⁻¹ *
        ∑ r ∈ Finset.range c.natAbs,
          ((Work.Peluse.symIcc (L / c.natAbs + 1)).card : ℝ) *
            Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 D)
              (Work.Peluse.symIcc (L / c.natAbs + 1)) (fun z : ℤ => F (c * z + (r : ℤ))) := by
  have hFfin : FinSuppZ F := FinSuppZ.of_supportIn hFs
  -- the dilates are finitely supported
  have hgr_supp : ∀ r : ℤ, SupportIn (fun z : ℤ => F (c * z + r)) (L + r.natAbs) := by
    intro r z hz
    apply hFs
    have h1 : (c * z).natAbs ≤ (c * z + r).natAbs + r.natAbs := by
      have h := Int.natAbs_add_le (c * z + r) (-r)
      simpa [Int.natAbs_neg, add_assoc] using h
    rw [Int.natAbs_mul] at h1
    have h2 : z.natAbs ≤ c.natAbs * z.natAbs :=
      Nat.le_mul_of_pos_left z.natAbs (Int.natAbs_pos.mpr hc)
    omega
  -- the summand vanishes far out
  have hpsi_supp : ∀ a b : ℤ, a ∈ arithIcc 1 D → b ∈ arithIcc 1 D → ∀ x : ℤ,
      L + 2 * (c.natAbs * D) + 2 < x.natAbs → psi c D F a b x = 0 := by
    intro a b ha hb x hx
    have hKa : a.natAbs ≤ D := mem_symIcc.mp (subset_symIcc_of_arithIcc_one ha)
    have hKb : b.natAbs ≤ D := mem_symIcc.mp (subset_symIcc_of_arithIcc_one hb)
    have hz : (∑ k ∈ arithIcc 1 D,
        F (x + c * a + c * k) * star (F (x + c * b + c * k))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hKk : k.natAbs ≤ D := mem_symIcc.mp (subset_symIcc_of_arithIcc_one hk)
      by_cases hF : F (x + c * a + c * k) = 0
      · simp [hF]
      · exfalso
        have hA : (x + c * a + c * k).natAbs ≤ L := by
          by_contra hcon
          exact hF (hFs _ (Nat.lt_of_not_le hcon))
        have ht1 : x.natAbs ≤ (x + c * a + c * k).natAbs + (c * a + c * k).natAbs := by
          have h := Int.natAbs_add_le (x + c * a + c * k) (-(c * a + c * k))
          rw [Int.natAbs_neg] at h
          have hL : x + c * a + c * k + -(c * a + c * k) = x := by ring
          rwa [hL] at h
        have ht2 : (c * a + c * k).natAbs ≤ c.natAbs * a.natAbs + c.natAbs * k.natAbs := by
          have h := Int.natAbs_add_le (c * a) (c * k)
          rw [Int.natAbs_mul, Int.natAbs_mul] at h
          exact h
        have hm1 : c.natAbs * a.natAbs ≤ c.natAbs * D := Nat.mul_le_mul_left c.natAbs hKa
        have hm2 : c.natAbs * k.natAbs ≤ c.natAbs * D := Nat.mul_le_mul_left c.natAbs hKk
        have hfin : x.natAbs ≤ L + 2 * (c.natAbs * D) := by omega
        omega
    simp only [psi, hz, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  -- the residue-class splitting of the `x`-sum
  have hsplit : ∀ a b : ℤ, a ∈ arithIcc 1 D → b ∈ arithIcc 1 D →
      ∑' x : ℤ, psi c D F a b x
        = ∑ r ∈ Finset.range c.natAbs, ∑' z : ℤ, psi c D F a b (c * z + (r : ℤ)) :=
    fun a b ha hb => tsum_mod_split_aux hc (N := L + 2 * (c.natAbs * D) + 2)
      (v := fun x => psi c D F a b x) (fun x hx => hpsi_supp a b ha hb x hx)
  -- reduction of the left-hand side
  have hA : (∑ a ∈ arithIcc c D, ∑ b ∈ arithIcc c D, ∑' x : ℤ,
        ‖∑ k ∈ arithIcc c D, F (x + a + k) * star (F (x + b + k))‖ ^ 2)
      = ∑ a ∈ arithIcc 1 D, ∑ b ∈ arithIcc 1 D, ∑' x : ℤ, psi c D F a b x := by
    rw [sum_arithIcc_c hc D (f := fun a : ℤ => ∑ b ∈ arithIcc c D, ∑' x : ℤ,
        ‖∑ k ∈ arithIcc c D, F (x + a + k) * star (F (x + b + k))‖ ^ 2)]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [sum_arithIcc_c hc D (f := fun b : ℤ => ∑' x : ℤ,
        ‖∑ k ∈ arithIcc c D, F (x + c * a + k) * star (F (x + b + k))‖ ^ 2)]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    refine tsum_congr (fun x => ?_)
    rw [sum_arithIcc_c hc D (f := fun k : ℤ =>
      F (x + c * a + k) * star (F (x + c * b + k)))]
    simp only [psi]
  have hLHS : boxNormPow 2 (fun _ : Fin 2 => arithIcc c D) (symIcc L) F
      = ((symIcc L).card : ℝ)⁻¹ * ((D : ℝ))⁻¹ ^ 4 *
        ∑ a ∈ arithIcc 1 D, ∑ b ∈ arithIcc 1 D, ∑' x : ℤ, psi c D F a b x := by
    rw [BoxNormDilation.boxNormPow_two_eq (arithIcc c D) (symIcc L) hFfin,
      card_arithIcc hc D, hA]
  -- reduction of each summand of the right-hand side
  have hRHS : ∀ r ∈ Finset.range c.natAbs,
      boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L / c.natAbs + 1))
            (fun z : ℤ => F (c * z + (r : ℤ)))
        = ((symIcc (L / c.natAbs + 1)).card : ℝ)⁻¹ * ((D : ℝ))⁻¹ ^ 4 *
          ∑ a ∈ arithIcc 1 D, ∑ b ∈ arithIcc 1 D, ∑' z : ℤ,
            psi c D F a b (c * z + (r : ℤ)) := by
    intro r hr
    rw [BoxNormDilation.boxNormPow_two_eq (arithIcc 1 D) (symIcc (L / c.natAbs + 1))
          (FinSuppZ.of_supportIn (hgr_supp r)), card_arithIcc one_ne_zero D]
    congr 1
    refine Finset.sum_congr rfl (fun a ha => ?_)
    refine Finset.sum_congr rfl (fun b hb => ?_)
    refine tsum_congr (fun z => ?_)
    simp only [psi]
    rw [show (∑ k ∈ arithIcc 1 D,
            F (c * (z + a + k) + (r : ℤ)) * star (F (c * (z + b + k) + (r : ℤ))))
          = (∑ k ∈ arithIcc 1 D,
            F (c * z + (r : ℤ) + c * a + c * k) *
              star (F (c * z + (r : ℤ) + c * b + c * k))) from by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [show c * (z + a + k) + (r : ℤ) = c * z + (r : ℤ) + c * a + c * k from by ring,
        show c * (z + b + k) + (r : ℤ) = c * z + (r : ℤ) + c * b + c * k from by ring]]
  -- the two sides agree
  have hAB : (∑ a ∈ arithIcc 1 D, ∑ b ∈ arithIcc 1 D, ∑' x : ℤ, psi c D F a b x)
      = ∑ r ∈ Finset.range c.natAbs, ∑ a ∈ arithIcc 1 D, ∑ b ∈ arithIcc 1 D,
          ∑' z : ℤ, psi c D F a b (c * z + (r : ℤ)) := by
    have h1 : (∑ a ∈ arithIcc 1 D, ∑ b ∈ arithIcc 1 D, ∑' x : ℤ, psi c D F a b x)
        = ∑ a ∈ arithIcc 1 D, ∑ b ∈ arithIcc 1 D, ∑ r ∈ Finset.range c.natAbs,
            ∑' z : ℤ, psi c D F a b (c * z + (r : ℤ)) := by
      refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
      exact hsplit a b ha hb
    rw [h1]
    calc ∑ a ∈ arithIcc 1 D, ∑ b ∈ arithIcc 1 D, ∑ r ∈ Finset.range c.natAbs,
            ∑' z : ℤ, psi c D F a b (c * z + (r : ℤ))
        = ∑ a ∈ arithIcc 1 D, ∑ r ∈ Finset.range c.natAbs, ∑ b ∈ arithIcc 1 D,
            ∑' z : ℤ, psi c D F a b (c * z + (r : ℤ)) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ r ∈ Finset.range c.natAbs, ∑ a ∈ arithIcc 1 D, ∑ b ∈ arithIcc 1 D,
            ∑' z : ℤ, psi c D F a b (c * z + (r : ℤ)) := Finset.sum_comm
  have hS'ne : ((symIcc (L / c.natAbs + 1)).card : ℝ) ≠ 0 := by
    rw [card_symIcc]; positivity
  have hRHS' : (∑ r ∈ Finset.range c.natAbs, ((symIcc (L / c.natAbs + 1)).card : ℝ) *
        boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc (L / c.natAbs + 1))
          (fun z : ℤ => F (c * z + (r : ℤ))))
      = ((D : ℝ))⁻¹ ^ 4 * ∑ r ∈ Finset.range c.natAbs, ∑ a ∈ arithIcc 1 D,
          ∑ b ∈ arithIcc 1 D, ∑' z : ℤ, psi c D F a b (c * z + (r : ℤ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [hRHS r hr]
    field_simp
  rw [hLHS, hAB, hRHS']
  ring

end

end Work.Peluse.Ulower
