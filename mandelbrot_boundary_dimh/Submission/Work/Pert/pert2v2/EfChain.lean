import Mathlib
import Submission.Work.Pert.pert2v2.EfFloor
import Submission.Work.Pert.pert2v2.HornExt

/-!
# `Work.Pert.pert2v2.EfChain` — the floor-based `Ef` at level `0`, its canonical representative,
and its `ℤ`-shifts

`pert2v2.end_const_le_seg` (the paper's (A.4.4)) is fed the floor-based `ℤ`-extension
`pert2v2.EfFloor Φm Φp Q`.  Three facts about it are needed, and they are elementary (no dynamics):

* **level `0`** (`EfFloor_level_of_re_mem`): at a gate value `Φm ς` whose real part lies in `[0,1)`,
  the canonical representative is `Φm ς` itself, hence `EfFloor (Φm ς) = Φp ς`;
* **the canonical representative is a gate value** (`EfFloor_canon_mem_of_cover`): from the
  pointwise form of the cover — `x + iy ∈ Φm '' Q` for every `x ∈ [0,1)` and every `y ≥ Y` — every
  `w` with `w.im ≥ Y` has its `⌊Re⌋`-representative in `Φm '' Q` (the representative's real part
  lies in `[0,1)` *by construction*, so the cover applies to it verbatim);
* **the `ℤ`-shift form** (`EfFloor_add_int_of_canon`): from `herb` and `EfFloor_add_one`, every
  integer shift shifts the value by the same integer.  (Same induction as
  `HornExt.Ef_add_int`, which is stated for the sibling `HornExt.Ef`.)
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- **The floor-based `Ef` at a gate value with real part in `[0,1)`.** -/
theorem EfFloor_level_of_re_mem {Φm Φp : ℂ → ℂ} {Q : Set ℂ} {ς : ℂ}
    (hinj : Set.InjOn Φm Q) (hς : ς ∈ Q)
    (h0 : 0 ≤ (Φm ς).re) (h1 : (Φm ς).re < 1) :
    EfFloor Φm Φp Q (Φm ς) = Φp ς := by
  classical
  have hfloor : ⌊(Φm ς).re⌋ = 0 := by
    rw [Int.floor_eq_iff]
    simp only [Int.cast_zero, zero_add]
    exact ⟨h0, h1⟩
  have hfloor' : (((⌊(Φm ς).re⌋ : ℤ)) : ℂ) = 0 := by
    rw [hfloor]; simp
  have hmem : Φm ς - (((⌊(Φm ς).re⌋ : ℤ)) : ℂ) ∈ Φm '' Q := by
    rw [hfloor']
    exact ⟨ς, hς, by simp⟩
  have hinv : Work.Pert.invOn Φm Q (Φm ς - (((⌊(Φm ς).re⌋ : ℤ)) : ℂ)) = ς := by
    rw [hfloor']
    exact Work.Pert.invOn_eq hinj (⟨ς, hς, by simp⟩) hς (by simp)
  unfold EfFloor
  rw [if_pos hmem, hinv, hfloor']
  ring

/-- **The canonical representative of `w` is a gate value**, above the cover's threshold. -/
theorem EfFloor_canon_mem_of_cover {Φm : ℂ → ℂ} {Q : Set ℂ} {Y : ℝ}
    (hcover : ∀ y x : ℝ, Y ≤ y → x ∈ Set.Ico (0 : ℝ) 1 →
      (x : ℂ) + (y : ℂ) * Complex.I ∈ Φm '' Q) :
    ∀ w : ℂ, Y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Q := by
  intro w hw
  set r : ℂ := w - (((⌊w.re⌋ : ℤ)) : ℂ) with hr
  have hre : r.re = w.re - ((⌊w.re⌋ : ℤ) : ℝ) := by simp [hr]
  have him : r.im = w.im := by simp [hr]
  have h1 : 0 ≤ r.re := by rw [hre]; exact sub_nonneg.mpr (Int.floor_le w.re)
  have h2 : r.re < 1 := by
    rw [hre]
    have := Int.lt_floor_add_one w.re
    linarith
  have hdecomp : r = (r.re : ℂ) + (r.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have h := hcover r.im r.re (by rw [him]; exact hw) ⟨h1, h2⟩
  rwa [hdecomp]

/-- **The `+1` relation of `EfFloor` on a half plane** (the `hper` of `end_const_le_seg`), from the
canonical-representative hypothesis `herb`. -/
theorem EfFloor_per_of_canon {Φm Φp : ℂ → ℂ} {Q : Set ℂ} {y : ℝ}
    (herb : ∀ w : ℂ, y ≤ w.im → w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ Φm '' Q) :
    ∀ u : ℂ, y ≤ u.im → EfFloor Φm Φp Q (u + 1) = EfFloor Φm Φp Q u + 1 :=
  fun u hu => EfFloor_add_one u (herb u hu)

/-- **The `ℤ`-shift form of `EfFloor`'s periodicity**, from its `+1` form on a half plane. -/
theorem EfFloor_add_int_of_per {Φm Φp : ℂ → ℂ} {Q : Set ℂ} {y : ℝ}
    (hper : ∀ u : ℂ, y ≤ u.im → EfFloor Φm Φp Q (u + 1) = EfFloor Φm Φp Q u + 1) :
    ∀ (k : ℤ) (u : ℂ), y ≤ u.im →
      EfFloor Φm Φp Q (u + (k : ℂ)) = EfFloor Φm Φp Q u + (k : ℂ) := by
  have hfwd : ∀ (m : ℕ) (u : ℂ), y ≤ u.im →
      EfFloor Φm Φp Q (u + (m : ℂ)) = EfFloor Φm Φp Q u + (m : ℂ) := by
    intro m
    induction m with
    | zero => intro u _; simp
    | succ k ih =>
      intro u hu
      have h1 : u + ((k + 1 : ℕ) : ℂ) = (u + (k : ℂ)) + 1 := by push_cast; ring
      rw [h1, hper _ (by simpa using hu), ih u hu]
      push_cast; ring
  have hbwd : ∀ (m : ℕ) (u : ℂ), y ≤ u.im →
      EfFloor Φm Φp Q (u - (m : ℂ)) = EfFloor Φm Φp Q u - (m : ℂ) := by
    intro m
    induction m with
    | zero => intro u _; simp
    | succ k ih =>
      intro u hu
      have h1 : u - ((k + 1 : ℕ) : ℂ) = (u - (k : ℂ)) - 1 := by push_cast; ring
      have h2 : ((u - (k : ℂ)) - 1) + 1 = u - (k : ℂ) := by ring
      have hstep := hper ((u - (k : ℂ)) - 1) (by simpa using hu)
      rw [h2] at hstep
      have hgoal : EfFloor Φm Φp Q ((u - (k : ℂ)) - 1)
          = EfFloor Φm Φp Q (u - (k : ℂ)) - 1 := eq_sub_iff_add_eq.mpr hstep.symm
      rw [h1, hgoal, ih u hu]
      push_cast; ring
  intro k u hu
  rcases lt_or_ge k 0 with hk | hk
  · have hcast : (((-k).toNat : ℕ) : ℂ) = -(k : ℂ) := by
      have h : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h
    have hkey : u + (k : ℂ) = u - (((-k).toNat : ℕ) : ℂ) := by rw [hcast]; ring
    rw [hkey, hbwd ((-k).toNat) u hu, hcast]
    ring
  · have hcast : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
      have h : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
      exact_mod_cast h
    rw [← hcast, hfwd k.toNat u hu]

end

end Work.Pert.pert2v2
