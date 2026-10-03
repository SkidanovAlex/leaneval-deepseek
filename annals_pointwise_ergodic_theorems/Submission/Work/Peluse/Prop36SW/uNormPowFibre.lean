import Mathlib
import Submission.Work.Peluse.LevelRaise.boxNormPow_succ_ge
import Submission.Work.Peluse.Prop36SW.tsumModSplit

/-!
# The fibre decomposition of the box-norm power along the arithmetic progression `c[L]`

For `c ≠ 0` the box-norm power with the *dilated* direction set `c[L] = {c, 2c, …, Lc}` and window
`[-N,N]` decomposes, over the residue classes modulo `|c|`, into the box-norm powers with the plain
direction set `[L]` of the `|c|` dilates `g_r z = f (c z + r)`, `r = 0, 1, …, |c|-1`,

`‖f‖^{2^t}_{□ᵗ_{c[L]}([-N,N])}
   = |[-N,N]|⁻¹ · ∑_{r < |c|} |[-M,M]| · ‖g_r‖^{2^t}_{□ᵗ_{[L]}([-M,M])}`,

*for every* window size `M`.  The window of the right-hand side only enters through the
normalisation `|[-M,M]|⁻¹`, which cancels against the explicit factor `|[-M,M]|`, so the identity is
independent of `M` (this is why `M` is a free parameter of the statement).

## Proof

The whole content is the identity of the *unnormalised* cube averages

`rawSum t (c[L]) f = ∑_{r < |c|} rawSum t ([L]) (g_r)`.

Indeed `boxNormPow t Q S f = boxScaling t Q S · ‖rawSum t Q f‖`, and `boxScaling t Q S` depends on
`Q` only through `∏_i |Q i| = L^t` and on `S` only through `|S|⁻¹`, so after multiplying back the
cancelling factors the two sides differ by exactly this identity (all the `rawSum`s involved are
nonnegative reals, `BoxNorm.rawSum_eq_cubeNormSqSum`, so taking moduli is legitimate).

The cube average itself is reindexed in two steps.

* The shift tuples of `c[L]` are `c` times the shift tuples of `[L]`, coordinatewise: the
  multiplication `n ↦ c n` is a bijection `[L] → c[L]` (`fibreEquiv`, `fibreEquivPi`), and it
  satisfies `cornerShift (c·h) (c·h') ω = c · cornerShift h h' ω`
  (`cornerShift_fibreEquivPi`).
* The `x`-sum splits into the residue classes modulo `c`: `x = c z + r` with `0 ≤ r < |c|`
  (`tsumModSplit`), which turns the cube term of `f` with corner shifts `c·cs(ω)` into the cube
  term of `g_r` with corner shifts `cs(ω)`.

## Main results

* `Work.Peluse.Prop36SW.rawSum_arithIcc_fibre`
* `Work.Peluse.Prop36SW.uNormPowFibre`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Prop36SW

open Work.Peluse

noncomputable section

/-! ## The fibre bijection `[L] → c[L]` -/

/-- For `c ≠ 0` the multiplication `n ↦ c * n` is a bijection from `[L] = {1, …, L}` onto the
dilated progression `c[L] = {c, 2c, …, Lc}`. -/
def fibreEquiv (c : ℤ) (hc : c ≠ 0) (L : ℕ) :
    {y : ℤ // y ∈ arithIcc 1 L} ≃ {y : ℤ // y ∈ arithIcc c L} :=
  Equiv.ofBijective
    (fun a : {y : ℤ // y ∈ arithIcc 1 L} =>
      ⟨c * a.1, by
        obtain ⟨n, hn, hna⟩ :=
          Finset.mem_image.mp (show a.1 ∈ (Finset.Icc 1 L).image (fun n : ℕ => (1 : ℤ) * (n : ℤ))
            from a.2)
        exact Finset.mem_image.mpr ⟨n, hn, by simp only [one_mul] at hna; rw [hna]⟩⟩)
    ⟨fun a a' h => Subtype.ext (mul_left_cancel₀ hc (congrArg Subtype.val h)),
     fun h => by
      obtain ⟨n, hn, hne⟩ := Finset.mem_image.mp h.2
      exact ⟨⟨(n : ℤ), Finset.mem_image.mpr ⟨n, hn, by simp⟩⟩, by
        apply Subtype.ext
        simpa using hne⟩⟩

/-- The coordinatewise version of `fibreEquiv` on the shift tuples of the cube. -/
def fibreEquivPi (t : ℕ) (c : ℤ) (hc : c ≠ 0) (L : ℕ) :
    ((i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L}) ≃ ((i : Fin t) → {y : ℤ // y ∈ arithIcc c L}) :=
  Equiv.piCongrRight (fun _ : Fin t => fibreEquiv c hc L)

lemma fibreEquivPi_apply_val {t : ℕ} {c : ℤ} (hc : c ≠ 0) (L : ℕ)
    (a : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L}) (i : Fin t) :
    ((fibreEquivPi t c hc L a) i).1 = c * (a i).1 := rfl

/-- The corner shifts of a `c`-dilated cube are `c` times the corner shifts of the original. -/
lemma cornerShift_fibreEquivPi {t : ℕ} {c : ℤ} (hc : c ≠ 0) (L : ℕ)
    (a a' : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L}) (ω : Fin t → Bool) :
    cornerShift (fun i => ((fibreEquivPi t c hc L a) i).1)
        (fun i => ((fibreEquivPi t c hc L a') i).1) ω
      = c * cornerShift (fun i => (a i).1) (fun i => (a' i).1) ω := by
  simp only [fibreEquivPi_apply_val, cornerShift, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by split <;> ring)

/-! ## Elementary facts about `arithIcc` and `boxScaling` -/

/-- For `c ≠ 0` the dilated progression `c[L]` has exactly `L` elements. -/
lemma card_arithIcc {c : ℤ} (hc : c ≠ 0) (L : ℕ) : (arithIcc c L).card = L := by
  rw [arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
    exact_mod_cast h

/-- The normalising constant of the box-norm power with the constant direction set `c[L]`. -/
lemma boxScaling_const (t : ℕ) {c : ℤ} (hc : c ≠ 0) (L : ℕ) (S : Finset ℤ) :
    BoxNorm.boxScaling t (fun _ : Fin t => arithIcc c L) S
      = (S.card : ℝ)⁻¹ * ((L : ℝ)⁻¹) ^ (2 * t) := by
  have h1 : (∏ _i : Fin t, (((fun _ : Fin t => arithIcc c L) _i).card : ℝ)⁻¹)
      = ((L : ℝ)⁻¹) ^ t := by
    rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [card_arithIcc hc L])]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ((L : ℝ)⁻¹) ^ t * ((L : ℝ)⁻¹) ^ t = ((L : ℝ)⁻¹) ^ (2 * t) := by
    rw [← pow_add, show t + t = 2 * t by ring]
  rw [BoxNorm.boxScaling, h1, mul_assoc, h2]

/-- The symmetric window is never empty. -/
lemma card_symIcc_ne_zero (M : ℕ) : ((symIcc M).card : ℝ) ≠ 0 := by
  have h : (symIcc M).card = 2 * M + 1 := by
    rw [symIcc, Int.card_Icc]
    have h1 : (M : ℤ) + 1 - (-(M : ℤ)) = (2 * M + 1 : ℕ) := by push_cast; ring
    rw [h1]
    exact Int.toNat_natCast (2 * M + 1)
  rw [h]
  positivity

/-! ## The fibre decomposition of the raw cube average -/

/-- **The fibre decomposition of the unnormalised cube average.**  The cube average over the
dilated direction set `c[L]` is the sum, over the residue classes `r` modulo `|c|`, of the cube
averages of the dilates `g_r z = f (c z + r)` over the direction set `[L]`. -/
theorem rawSum_arithIcc_fibre (t : ℕ) (κ : ℤ) (hκ : κ ≠ 0) (L N : ℕ) (f : ℤ → ℂ)
    (hsup : SupportIn f N) :
    BoxNorm.rawSum t (fun _ : Fin t => arithIcc κ L) f
      = ∑ r ∈ Finset.range κ.natAbs,
          BoxNorm.rawSum t (fun _ : Fin t => arithIcc 1 L)
            (fun z : ℤ => f (κ * z + (r : ℤ))) := by
  classical
  -- (1) reindex the shift tuples of the outer double sum
  have h1 : BoxNorm.rawSum t (fun _ : Fin t => arithIcc κ L) f
      = ∑ a : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
          ∑ a' : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L}, ∑' x : ℤ,
            ∏ ω : Fin t → Bool, (star^[weight ω])
              (f (x + cornerShift
                    (fun i => ((fibreEquivPi t κ hκ L a) i).1)
                    (fun i => ((fibreEquivPi t κ hκ L a') i).1) ω)) := by
    simp only [BoxNorm.rawSum]
    rw [← Equiv.sum_comp (fibreEquivPi t κ hκ L)
      (fun h : ((i : Fin t) → {y : ℤ // y ∈ arithIcc κ L}) =>
        ∑ h' : ((i : Fin t) → {y : ℤ // y ∈ arithIcc κ L}), ∑' x : ℤ,
          ∏ ω : Fin t → Bool, (star^[weight ω])
            (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Equiv.sum_comp (fibreEquivPi t κ hκ L)
      (fun h' : ((i : Fin t) → {y : ℤ // y ∈ arithIcc κ L}) => ∑' x : ℤ,
        ∏ ω : Fin t → Bool, (star^[weight ω])
          (f (x + cornerShift (fun i => ((fibreEquivPi t κ hκ L a) i).1)
                (fun i => (h' i).1) ω)))]
  -- (2) split each `x`-sum into residue classes
  have hsplit : ∀ a a' : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
      (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
        (f (x + cornerShift (fun i => ((fibreEquivPi t κ hκ L a) i).1)
              (fun i => ((fibreEquivPi t κ hκ L a') i).1) ω)))
        = ∑ r ∈ Finset.range κ.natAbs, ∑' z : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
            ((fun z : ℤ => f (κ * z + (r : ℤ)))
              (z + cornerShift (fun i => (a i).1) (fun i => (a' i).1) ω)) := by
    intro a a'
    have hv : ∀ x : ℤ, N + ∑ i : Fin t, (arithIcc κ L).sum (fun z => z.natAbs) < x.natAbs →
        (∏ ω : Fin t → Bool, (star^[weight ω])
          (f (x + cornerShift (fun i => ((fibreEquivPi t κ hκ L a) i).1)
                (fun i => ((fibreEquivPi t κ hκ L a') i).1) ω))) = 0 := by
      intro x hx
      refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin t => false)) ?_
      have hle : (cornerShift (fun i => ((fibreEquivPi t κ hκ L a) i).1)
            (fun i => ((fibreEquivPi t κ hκ L a') i).1) (fun _ : Fin t => false)).natAbs
          ≤ ∑ i : Fin t, (arithIcc κ L).sum (fun z => z.natAbs) :=
        BoxNorm.cornerShift_natAbs_le (fun _ : Fin t => arithIcc κ L)
          (fibreEquivPi t κ hκ L a) (fibreEquivPi t κ hκ L a') (fun _ => false)
      have hgt : N < (x + cornerShift (fun i => ((fibreEquivPi t κ hκ L a) i).1)
            (fun i => ((fibreEquivPi t κ hκ L a') i).1) (fun _ : Fin t => false)).natAbs := by
        have htri := Int.natAbs_add_le
          (x + cornerShift (fun i => ((fibreEquivPi t κ hκ L a) i).1)
            (fun i => ((fibreEquivPi t κ hκ L a') i).1) (fun _ : Fin t => false))
          (-(cornerShift (fun i => ((fibreEquivPi t κ hκ L a) i).1)
            (fun i => ((fibreEquivPi t κ hκ L a') i).1) (fun _ : Fin t => false)))
        simp only [Int.natAbs_neg, add_neg_cancel_right] at htri
        omega
      rw [hsup _ hgt, BoxNorm.star_iterate_zero_eq_zero]
    rw [tsumModSplit hκ hv]
    refine Finset.sum_congr rfl (fun r _ => tsum_congr (fun z => ?_))
    refine Finset.prod_congr rfl (fun ω _ => ?_)
    simp only
    rw [cornerShift_fibreEquivPi hκ L a a' ω]
    congr 1
    ring_nf
  -- (3) reassemble
  rw [h1]
  refine (Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun a' _ => hsplit a a'))).trans ?_
  have hswap : (∑ a : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
        ∑ a' : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
          ∑ r ∈ Finset.range κ.natAbs, ∑' z : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
            ((fun z : ℤ => f (κ * z + (r : ℤ)))
              (z + cornerShift (fun i => (a i).1) (fun i => (a' i).1) ω)))
      = ∑ r ∈ Finset.range κ.natAbs,
          ∑ a : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
            ∑ a' : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
              ∑' z : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
                ((fun z : ℤ => f (κ * z + (r : ℤ)))
                  (z + cornerShift (fun i => (a i).1) (fun i => (a' i).1) ω)) := by
    calc ∑ a : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
            ∑ a' : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
              ∑ r ∈ Finset.range κ.natAbs, ∑' z : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
                ((fun z : ℤ => f (κ * z + (r : ℤ)))
                  (z + cornerShift (fun i => (a i).1) (fun i => (a' i).1) ω))
        = ∑ a : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
            ∑ r ∈ Finset.range κ.natAbs,
              ∑ a' : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
                ∑' z : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
                  ((fun z : ℤ => f (κ * z + (r : ℤ)))
                    (z + cornerShift (fun i => (a i).1) (fun i => (a' i).1) ω)) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ r ∈ Finset.range κ.natAbs,
            ∑ a : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
              ∑ a' : (i : Fin t) → {y : ℤ // y ∈ arithIcc 1 L},
                ∑' z : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
                  ((fun z : ℤ => f (κ * z + (r : ℤ)))
                    (z + cornerShift (fun i => (a i).1) (fun i => (a' i).1) ω)) :=
          Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rfl

/-- A raw cube average of a finitely supported function is a nonnegative real. -/
lemma rawSum_eq_ofReal_norm (t : ℕ) (ht : 1 ≤ t) (Q : Fin t → Finset ℤ) {f : ℤ → ℂ}
    (hf : FinSuppZ f) :
    BoxNorm.rawSum t Q f = ((‖BoxNorm.rawSum t Q f‖ : ℝ) : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  obtain ⟨N, hN⟩ := hf
  rw [BoxNorm.rawSum_eq_cubeNormSqSum Q f hN,
    Complex.norm_of_nonneg (BoxNorm.normSqSum_nonneg Q f N)]

theorem uNormPowFibre (t : ℕ) (ht : 1 ≤ t) (κ : ℤ) (hκ : κ ≠ 0) (L N M : ℕ) (f : ℤ → ℂ) (hsup : Work.Peluse.SupportIn f N) :
    Work.Peluse.uNormPow t (Work.Peluse.arithIcc κ L) (Work.Peluse.symIcc N) f
      = ((Work.Peluse.symIcc N).card : ℝ)⁻¹ *
        ∑ r ∈ Finset.range κ.natAbs,
          ((Work.Peluse.symIcc M).card : ℝ) *
            Work.Peluse.uNormPow t (Work.Peluse.arithIcc (1 : ℤ) L) (Work.Peluse.symIcc M)
              (fun z : ℤ => f (κ * z + (r : ℤ))) := by
  classical
  -- the dilates are finitely supported
  have hgsup : ∀ r ∈ Finset.range κ.natAbs,
      SupportIn (fun z : ℤ => f (κ * z + (r : ℤ))) (N + κ.natAbs) := by
    intro r hr z hz
    apply hsup
    have hrlt : r < κ.natAbs := Finset.mem_range.mp hr
    have h1 : (κ * z).natAbs ≤ (κ * z + (r : ℤ)).natAbs + (r : ℤ).natAbs := by
      have h := Int.natAbs_add_le (κ * z + (r : ℤ)) (-(r : ℤ))
      simpa [Int.natAbs_neg, add_assoc] using h
    rw [Int.natAbs_natCast] at h1
    have h2 : z.natAbs ≤ (κ * z).natAbs := by
      rw [Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hκ)
    omega
  -- each raw cube average of a dilate is a nonnegative real
  have hraw : ∀ r ∈ Finset.range κ.natAbs,
      BoxNorm.rawSum t (fun _ : Fin t => arithIcc 1 L) (fun z : ℤ => f (κ * z + (r : ℤ)))
        = ((‖BoxNorm.rawSum t (fun _ : Fin t => arithIcc 1 L)
            (fun z : ℤ => f (κ * z + (r : ℤ)))‖ : ℝ) : ℂ) :=
    fun r hr => rawSum_eq_ofReal_norm t ht (fun _ : Fin t => arithIcc 1 L)
      (FinSuppZ.of_supportIn (hgsup r hr))
  -- hence the moduli add up
  have hnorm : ‖BoxNorm.rawSum t (fun _ : Fin t => arithIcc κ L) f‖
      = ∑ r ∈ Finset.range κ.natAbs,
          ‖BoxNorm.rawSum t (fun _ : Fin t => arithIcc 1 L)
            (fun z : ℤ => f (κ * z + (r : ℤ)))‖ := by
    have h2 : (∑ r ∈ Finset.range κ.natAbs,
          BoxNorm.rawSum t (fun _ : Fin t => arithIcc 1 L)
            (fun z : ℤ => f (κ * z + (r : ℤ))))
        = ((∑ r ∈ Finset.range κ.natAbs,
            ‖BoxNorm.rawSum t (fun _ : Fin t => arithIcc 1 L)
              (fun z : ℤ => f (κ * z + (r : ℤ)))‖ : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun r hr => hraw r hr)
    rw [rawSum_arithIcc_fibre t κ hκ L N f hsup, h2,
      Complex.norm_of_nonneg (Finset.sum_nonneg (fun r _ => norm_nonneg _))]
  -- the two normalised forms
  have hL : uNormPow t (arithIcc κ L) (symIcc N) f
      = ((symIcc N).card : ℝ)⁻¹ * ((L : ℝ)⁻¹) ^ (2 * t) *
          ‖BoxNorm.rawSum t (fun _ : Fin t => arithIcc κ L) f‖ := by
    show boxNormPow t (fun _ : Fin t => arithIcc κ L) (symIcc N) f = _
    rw [LevelRaise.boxNormPow_eq_scaling_mul_norm, boxScaling_const t hκ L (symIcc N)]
  have hR : ∀ r : ℕ, uNormPow t (arithIcc 1 L) (symIcc M) (fun z : ℤ => f (κ * z + (r : ℤ)))
      = ((symIcc M).card : ℝ)⁻¹ * (((L : ℝ)⁻¹) ^ (2 * t) *
          ‖BoxNorm.rawSum t (fun _ : Fin t => arithIcc 1 L)
            (fun z : ℤ => f (κ * z + (r : ℤ)))‖) := by
    intro r
    show boxNormPow t (fun _ : Fin t => arithIcc 1 L) (symIcc M)
      (fun z : ℤ => f (κ * z + (r : ℤ))) = _
    rw [LevelRaise.boxNormPow_eq_scaling_mul_norm,
      boxScaling_const t (c := (1 : ℤ)) one_ne_zero L (symIcc M)]
    ring
  have hRHS : (∑ r ∈ Finset.range κ.natAbs, ((symIcc M).card : ℝ) *
        uNormPow t (arithIcc 1 L) (symIcc M) (fun z : ℤ => f (κ * z + (r : ℤ))))
      = ((L : ℝ)⁻¹) ^ (2 * t) *
        ∑ r ∈ Finset.range κ.natAbs,
          ‖BoxNorm.rawSum t (fun _ : Fin t => arithIcc 1 L)
            (fun z : ℤ => f (κ * z + (r : ℤ)))‖ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [hR r, ← mul_assoc, mul_inv_cancel₀ (card_symIcc_ne_zero M), one_mul]
  rw [hL, hnorm, hRHS]
  ring

end

end Work.Peluse.Prop36SW
