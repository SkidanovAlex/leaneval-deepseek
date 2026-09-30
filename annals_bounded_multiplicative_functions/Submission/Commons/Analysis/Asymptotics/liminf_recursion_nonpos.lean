import Mathlib
import Submission.Commons.Analysis.Asymptotics.exponent_recursion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-sided limit inferior at `0⁺` and the liminf step of the exponent bootstrap

We develop the elementary order-theoretic machinery for the one-sided limit inferior of a real
function as `b → 0⁺`, defined (under local boundedness) as the supremum of the reals that bound
the function from below eventually.  We then use it to prove the liminf step of the exponent
bootstrap in Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ² decoupling for the moment curve*
(arXiv:1912.09798), §4: summing the recursion inequality after taking liminf makes all the
intermediate exponents cancel, leaving `liminf β₀ ≤ 0`.
-/

namespace Commons.Analysis.Asymptotics

open Filter

/-- The set of reals `m` that bound `f` from below eventually as `b → 0⁺`. -/
def evLower (f : ℝ → ℝ) : Set ℝ :=
  {m : ℝ | ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ f b}

/-- The one-sided limit inferior at `0⁺`, as the supremum of the eventual lower bounds. -/
noncomputable def liminfAt0 (f : ℝ → ℝ) : ℝ := sSup (evLower f)

theorem mem_evLower_iff {f : ℝ → ℝ} {m : ℝ} :
    m ∈ evLower f ↔ ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ f b := Iff.rfl

theorem liminfAt0_eq (f : ℝ → ℝ) : liminfAt0 f = sSup (evLower f) := rfl

theorem evLower_mono {f g : ℝ → ℝ}
    (h : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), f b ≤ g b) : evLower f ⊆ evLower g := by
  intro m hm
  filter_upwards [hm, h] with b hb hb'
  exact le_trans hb hb'

theorem evLower_nonempty_of_abs {f : ℝ → ℝ} {M : ℝ}
    (h : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |f b| ≤ M) : (evLower f).Nonempty :=
  ⟨-M, by filter_upwards [h] with b hb; exact (abs_le.mp hb).1⟩

theorem evLower_bddAbove_of_abs {f : ℝ → ℝ} {M : ℝ}
    (h : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |f b| ≤ M) : BddAbove (evLower f) := by
  refine ⟨M, fun m hm => ?_⟩
  have hm' : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ f b := hm
  rcases (hm'.and h).exists with ⟨b, h1, h2⟩
  exact le_trans h1 (abs_le.mp h2).2

theorem lt_liminfAt0 {f : ℝ → ℝ} (hne : (evLower f).Nonempty) (hbdd : BddAbove (evLower f))
    {m : ℝ} (hm : m < liminfAt0 f) :
    ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), m ≤ f b := by
  obtain ⟨m', hm', hlt⟩ := (lt_csSup_iff hbdd hne).mp hm
  filter_upwards [hm'] with b hb
  exact le_trans hlt.le hb

theorem liminfAt0_mono {f g : ℝ → ℝ} {Mf Mg : ℝ}
    (h : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), f b ≤ g b)
    (hf : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |f b| ≤ Mf)
    (hg : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |g b| ≤ Mg) :
    liminfAt0 f ≤ liminfAt0 g :=
  csSup_le_csSup (evLower_bddAbove_of_abs hg) (evLower_nonempty_of_abs hf) (evLower_mono h)

theorem liminfAt0_add_le {f g : ℝ → ℝ} {Mf Mg : ℝ}
    (hf : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |f b| ≤ Mf)
    (hg : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |g b| ≤ Mg) :
    liminfAt0 f + liminfAt0 g ≤ liminfAt0 (f + g) := by
  have hfne := evLower_nonempty_of_abs hf
  have hfbdd := evLower_bddAbove_of_abs hf
  have hgne := evLower_nonempty_of_abs hg
  have hgbdd := evLower_bddAbove_of_abs hg
  have hfgbdd : BddAbove (evLower (f + g)) := by
    have hb : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |(f + g) b| ≤ Mf + Mg := by
      filter_upwards [hf, hg] with b hb1 hb2
      calc |(f + g) b| = |f b + g b| := by rw [Pi.add_apply]
        _ ≤ |f b| + |g b| := abs_add_le _ _
        _ ≤ Mf + Mg := add_le_add hb1 hb2
    exact evLower_bddAbove_of_abs hb
  apply le_of_forall_pos_le_add
  intro e he
  have he2 : (0 : ℝ) < e / 2 := by linarith
  have h1 : liminfAt0 f - e / 2 < liminfAt0 f := by linarith
  have h2 : liminfAt0 g - e / 2 < liminfAt0 g := by linarith
  have e1' := lt_liminfAt0 hfne hfbdd h1
  have e2' := lt_liminfAt0 hgne hgbdd h2
  have e3 : ((liminfAt0 f - e / 2) + (liminfAt0 g - e / 2)) ∈ evLower (f + g) := by
    show ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (liminfAt0 f - e / 2) + (liminfAt0 g - e / 2) ≤ (f + g) b
    filter_upwards [e1', e2'] with b hb1 hb2
    rw [Pi.add_apply]
    linarith
  have h4 : (liminfAt0 f - e / 2) + (liminfAt0 g - e / 2) ≤ liminfAt0 (f + g) :=
    le_csSup hfgbdd e3
  linarith

theorem liminfAt0_smul (w : ℝ) (hw : 0 < w) {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |f b| ≤ M) :
    liminfAt0 (fun b => w * f b) = w * liminfAt0 f := by
  have hne := evLower_nonempty_of_abs hf
  have hbdd := evLower_bddAbove_of_abs hf
  have hg : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |(fun b => w * f b) b| ≤ w * M := by
    filter_upwards [hf] with b hb
    rw [abs_mul, abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left hb hw.le
  have hne' := evLower_nonempty_of_abs hg
  have hbdd' := evLower_bddAbove_of_abs hg
  apply le_antisymm
  · apply csSup_le hne'
    intro m hm
    have hm' : m / w ∈ evLower f := by
      show ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), m / w ≤ f b
      filter_upwards [hm] with b hb
      rw [div_le_iff₀ hw]
      calc m ≤ w * f b := hb
        _ = f b * w := by ring
    have hle : m / w ≤ liminfAt0 f := le_csSup hbdd hm'
    rw [div_le_iff₀ hw] at hle
    calc m ≤ liminfAt0 f * w := hle
      _ = w * liminfAt0 f := by ring
  · apply le_of_forall_pos_le_add
    intro e he
    have hew : 0 < e / w := div_pos he hw
    have hm : liminfAt0 f - e / w < liminfAt0 f := by linarith
    have hmem := lt_liminfAt0 hne hbdd hm
    have hmem' : w * (liminfAt0 f - e / w) ∈ evLower (fun b => w * f b) := by
      show ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), w * (liminfAt0 f - e / w) ≤ w * f b
      filter_upwards [hmem] with b hb
      exact mul_le_mul_of_nonneg_left hb hw.le
    have hle : w * (liminfAt0 f - e / w) ≤ liminfAt0 (fun b => w * f b) :=
      le_csSup hbdd' hmem'
    have hkey : w * (liminfAt0 f - e / w) = w * liminfAt0 f - e := by field_simp
    linarith

/-- Scaling the argument of a function by a positive constant does not change its one-sided
limit inferior at `0⁺`. -/
theorem nhdsGT_mul_eventually_iff {c : ℝ} (hc : 0 < c) (p : ℝ → Prop) :
    (∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), p (c * b)) ↔
    (∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), p b) := by
  have himg : (fun b : ℝ => c * b) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact mul_pos hc hb
    · intro hy
      exact ⟨y / c, div_pos hy hc, by field_simp⟩
  have hmap : Filter.map (fun b : ℝ => c * b) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      = nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    have h := (Homeomorph.mulLeft₀ c hc.ne').isEmbedding.map_nhdsWithin_eq (Set.Ioi 0) 0
    rw [Homeomorph.coe_mulLeft₀] at h
    have h0 : (fun x : ℝ => c * x) 0 = 0 := by simp
    rw [h, himg, h0]
  rw [Filter.eventually_iff, Filter.eventually_iff]
  change (fun b : ℝ => c * b) ⁻¹' {y : ℝ | p y} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) ↔
    {b : ℝ | p b} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)
  rw [← Filter.mem_map, hmap]

theorem liminfAt0_comp_mul {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    liminfAt0 (fun b => f (c * b)) = liminfAt0 f := by
  unfold liminfAt0 evLower
  congr 1
  ext m
  exact nhdsGT_mul_eventually_iff hc (fun y => m ≤ f y)

/-- GLYZ §4, the liminf step of the exponent bootstrap.

Let `k ≥ 2` and let `β : ℕ → ℝ → ℝ` be a family of real functions of the small parameter
`b > 0`, each locally bounded near `0⁺` (from above and below), satisfying, for every
`l ∈ {1, …, k-1}`, the pointwise recursion

  `β l b ≥ (1/l) · β (k-l) (((k-l+1)/l) · b) + ((k-l)/(k-l+1)) · β (l-1) b`

for all sufficiently small `b > 0`.  Then `β 0` does not eventually dominate any positive
number, i.e. `liminf_{b→0+} β 0 b ≤ 0`.

This is the exact algebraic core of the proof that the decoupling exponent is `0` in
Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ² decoupling for the moment curve*
(arXiv:1912.09798), §4: summing the inequality for `l = 1, …, k-1` after taking liminf
(using that `b ↦ ((k-l+1)/l)b` tends to `0⁺`, so the liminf is unchanged) makes all the
`β l` with `1 ≤ l ≤ k-1` cancel, leaving `0 ≥ liminf β 0`. -/
theorem liminf_recursion_nonpos {k : ℕ} (hk : 2 ≤ k) (β : ℕ → ℝ → ℝ)
    (hbdd : ∀ l ≤ k, ∃ M : ℝ, ∀ᶠ b in nhdsWithin (0:ℝ) (Set.Ioi 0), |β l b| ≤ M)
    (hrec : ∀ l, 1 ≤ l → l ≤ k - 1 → ∀ᶠ b in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (1 / (l : ℝ)) * β (k - l) ((((k : ℝ) - l + 1) / (l : ℝ)) * b)
        + (((k : ℝ) - l) / ((k : ℝ) - l + 1)) * β (l - 1) b ≤ β l b) :
    ∀ a : ℝ, 0 < a → ¬ (∀ᶠ b in nhdsWithin (0:ℝ) (Set.Ioi 0), a ≤ β 0 b) := by
  have hmain : ∀ l, 1 ≤ l → l ≤ k - 1 →
      (1 / (l : ℝ)) * liminfAt0 (β (k - l))
        + ((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1) * liminfAt0 (β (l - 1))
      ≤ liminfAt0 (β l) := by
    intro l hl1 hl2
    have hlk : l ≤ k := by omega
    obtain ⟨M1, hM1⟩ := hbdd (k - l) (by omega)
    obtain ⟨M2, hM2⟩ := hbdd (l - 1) (by omega)
    obtain ⟨M3, hM3⟩ := hbdd l hlk
    have hlpos : (0 : ℝ) < (l : ℝ) := by
      have : (0 : ℕ) < l := by omega
      exact_mod_cast this
    have hklcast : ((k - l : ℕ) : ℝ) = (k : ℝ) - (l : ℝ) := Nat.cast_sub hlk
    have hklpos : (0 : ℝ) < (k : ℝ) - (l : ℝ) := by
      rw [← hklcast]
      have : (0 : ℕ) < k - l := by omega
      exact_mod_cast this
    have hden : (0 : ℝ) < (k : ℝ) - (l : ℝ) + 1 := by linarith
    set c : ℝ := ((k : ℝ) - l + 1) / (l : ℝ) with hcdef
    set w : ℝ := ((k : ℝ) - l) / ((k : ℝ) - l + 1) with hwdef
    have hcpos : 0 < c := by rw [hcdef]; exact div_pos hden hlpos
    have hwpos : 0 < w := by rw [hwdef]; exact div_pos hklpos hden
    set f1 : ℝ → ℝ := fun b => (1 / (l : ℝ)) * β (k - l) (c * b) with hf1def
    set f2 : ℝ → ℝ := fun b => w * β (l - 1) b with hf2def
    have hliv : (0 : ℝ) < 1 / (l : ℝ) := one_div_pos.mpr hlpos
    have hc_ev : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |β (k - l) (c * b)| ≤ M1 :=
      (nhdsGT_mul_eventually_iff hcpos (fun y => |β (k - l) y| ≤ M1)).mpr hM1
    have hf1b : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |f1 b| ≤ (1 / (l : ℝ)) * M1 := by
      filter_upwards [hc_ev] with b hb
      rw [hf1def, abs_mul, abs_of_pos hliv]
      exact mul_le_mul_of_nonneg_left hb hliv.le
    have hf2b : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), |f2 b| ≤ w * M2 := by
      filter_upwards [hM2] with b hb
      rw [hf2def, abs_mul, abs_of_pos hwpos]
      exact mul_le_mul_of_nonneg_left hb hwpos.le
    have hL1 : liminfAt0 f1 = (1 / (l : ℝ)) * liminfAt0 (β (k - l)) := by
      rw [hf1def, liminfAt0_smul (1 / (l : ℝ)) hliv hc_ev, liminfAt0_comp_mul hcpos]
    have hL2 : liminfAt0 f2 = w * liminfAt0 (β (l - 1)) := by
      rw [hf2def]
      exact liminfAt0_smul w hwpos hM2
    have hrec' : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0), (f1 + f2) b ≤ β l b := by
      rw [hf1def, hf2def, hcdef, hwdef]
      exact hrec l hl1 hl2
    have hf12b : ∀ᶠ b in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        |(f1 + f2) b| ≤ (1 / (l : ℝ)) * M1 + w * M2 := by
      filter_upwards [hf1b, hf2b] with b hb1 hb2
      calc |(f1 + f2) b| = |f1 b + f2 b| := by rw [Pi.add_apply]
        _ ≤ |f1 b| + |f2 b| := abs_add_le _ _
        _ ≤ (1 / (l : ℝ)) * M1 + w * M2 := add_le_add hb1 hb2
    have hadd := liminfAt0_add_le hf1b hf2b
    have hmono := liminfAt0_mono hrec' hf12b hM3
    have hw_eq : w = ((k - l : ℕ) : ℝ) / ((k - l : ℕ) + 1) := by
      rw [hwdef, hklcast]
    rw [← hw_eq, ← hL1, ← hL2]
    linarith
  have hA0 : liminfAt0 (β 0) ≤ 0 :=
    exponent_recursion hk (fun n => liminfAt0 (β n)) hmain
  intro a ha hev
  obtain ⟨M0, hM0⟩ := hbdd 0 (by omega)
  have hle : a ≤ liminfAt0 (β 0) := le_csSup (evLower_bddAbove_of_abs hM0) hev
  linarith

end Commons.Analysis.Asymptotics
