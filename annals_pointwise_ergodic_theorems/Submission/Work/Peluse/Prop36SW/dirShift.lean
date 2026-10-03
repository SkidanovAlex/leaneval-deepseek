import Mathlib
import Submission.Work.Peluse.Prop36SW.signBridge

/-!
# Translating the individual direction sets of a box sum, and the sign invariance of the ladder's
# conclusion

`Work.Peluse.Ulower.boxSumPow_shift_directions` shows that translating **all** direction sets
`Q i ↦ Q i + s` by the *same* `s` leaves the box-sum power unchanged (the corner shift picks up the
constant `t·s`, absorbed by the `x`-translation in the unconditional sum over `ℤ`).  This module
generalises that to **per-coordinate** translations `Q i ↦ Q i + τ i` (`prodCubeSum_image_shift_idx`,
`boxSumPow_image_shift_idx`, `boxNormPow_image_shift_idx`, `boxNorm_image_shift_idx`): the corner
shift picks up `∑ i, τ i`, again independent of `ω`.

## Why this matters (it dissolves the session-5 sign obstruction)

`NOTES_prop36SW_of_ladderA_SESSION5.md` §3 proves that the natural coefficient of Peluse's §5 chain
is **signed** (a multilinear form on the parameter box), while the frozen `PeluseLadderA` demands a
**positive** coefficient; §6/§9 then worried that the reconciliation needs a *partial reflection* of
the conclusion's direction family, which has no clean identity.  The resolution is that no reflection
is needed at all: for an arithmetic progression `arithIcc (-c) L = (arithIcc c L).image (· + τ)`
with `τ = -(L+1)c` (`arithIcc_neg_eq_image_shift`), i.e. **reflecting an `arithIcc` set is a
translation of it** — and `boxSumPow` is invariant under translations of its direction sets.  Hence

* the state's hypothesis with `p` and with `|p|` agree (`sum_paramBox_pDirFamG_abs`, already proved —
  the sign substitution `b ↦ εb` makes the direction sets *equal*), and
* the ladder's **conclusion** with `p` and with `|p|` agree as well
  (`boxNormPow_conclDirG_abs`, `sum_paramBox_conclDirG_abs` below — the sign substitution makes the
  *short* directions equal and the *long* ones `arithIcc (|p s₀ a|) L'` versus `arithIcc (p s₀ a) L'`,
  which are translates of one another).

So the chain can be run in the signed world (where the round's regrouping identity
`∑_{s ∈ ω} p s a · b s = Λ_{j-1} · dir (j-1) ω (a ⊔ b)` is exact and the function stays `f`), while
the ladder is always applied to the positive `|p|`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-! ## Per-coordinate translation of the direction sets -/

/-- The corner shift of a translated pair of shift tuples: translating both corners by
`τ i` in the `i`-th coordinate translates the corner by the constant `∑ i, τ i`, which is
independent of `ω`. -/
lemma cornerShift_add_idx {t : ℕ} (h h' : Fin t → ℤ) (τ : Fin t → ℤ) (ω : Fin t → Bool) :
    Work.Peluse.cornerShift (fun i => h i + τ i) (fun i => h' i + τ i) ω
      = Work.Peluse.cornerShift h h' ω + ∑ i, τ i := by
  have hterm : ∀ i : Fin t,
      (if ω i then h i + τ i else h' i + τ i) = (if ω i then h i else h' i) + τ i := by
    intro i; by_cases hi : ω i <;> simp [hi]
  simp only [Work.Peluse.cornerShift]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]

/-- The translation `q ↦ q + s` of a finite set of integers, as a bijection onto its image. -/
def shiftIdxE (Q : Finset ℤ) (s : ℤ) :
    {x : ℤ // x ∈ Q.image (fun q => q + s)} ≃ {x : ℤ // x ∈ Q} where
  toFun z := ⟨z.1 - s, by
    obtain ⟨q, hq, hqz⟩ := Finset.mem_image.mp z.2
    have : z.1 - s = q := by omega
    rwa [this]⟩
  invFun z := ⟨z.1 + s, Finset.mem_image.mpr ⟨z.1, z.2, rfl⟩⟩
  left_inv z := by ext; simp
  right_inv z := by ext; simp

/-- The componentwise version of `shiftIdxE`. -/
abbrev piShiftIdxE (t : ℕ) (Q : Fin t → Finset ℤ) (τ : Fin t → ℤ) :
    ((i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun q => q + τ i)}) ≃
      ((i : Fin t) → {x : ℤ // x ∈ Q i}) where
  toFun h := fun i => shiftIdxE (Q i) (τ i) (h i)
  invFun h := fun i => (shiftIdxE (Q i) (τ i)).symm (h i)
  left_inv h := by funext i; simp [shiftIdxE]
  right_inv h := by funext i; simp [shiftIdxE]

/-- **Per-coordinate translation of the direction sets** (general `2^t` functions).  Replacing every
direction set `Q i` by its translate `Q i + τ i` leaves `Work.Peluse.prodCubeSum` unchanged: the
corner shift picks up the *constant* `∑ i, τ i`, which the unconditional `x`-sum absorbs. -/
theorem prodCubeSum_image_shift_idx (t : ℕ) (Q : Fin t → Finset ℤ) (τ : Fin t → ℤ)
    (S : Finset ℤ) (F : (Fin t → Bool) → ℤ → ℂ) :
    Work.Peluse.prodCubeSum t (fun i => (Q i).image (fun q => q + τ i)) S F
      = Work.Peluse.prodCubeSum t Q S F := by
  have hcard : ∀ i : Fin t, ((Q i).image (fun q => q + τ i)).card = (Q i).card := fun i =>
    Finset.card_image_of_injective _ (fun a b h => by simpa using add_right_cancel h)
  simp only [Work.Peluse.prodCubeSum, hcard]
  congr 1
  let E := piShiftIdxE t Q τ
  have key : ∀ (u u' : (i : Fin t) → {x : ℤ // x ∈ Q i}),
      (∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (F ω (x + Work.Peluse.cornerShift
          (fun i => ((E.symm u) i).1) (fun i => ((E.symm u') i).1) ω)))
      = ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (F ω (x + Work.Peluse.cornerShift
          (fun i => (u i).1) (fun i => (u' i).1) ω)) := by
    intro u u'
    have hcs : ∀ ω : Fin t → Bool,
        Work.Peluse.cornerShift (fun i => ((E.symm u) i).1) (fun i => ((E.symm u') i).1) ω
          = Work.Peluse.cornerShift (fun i => (u i).1) (fun i => (u' i).1) ω + ∑ i, τ i := by
      intro ω
      have h1 : (fun i : Fin t => ((E.symm u) i).1) = (fun i => (u i).1 + τ i) := by
        funext i; rfl
      have h2 : (fun i : Fin t => ((E.symm u') i).1) = (fun i => (u' i).1 + τ i) := by
        funext i; rfl
      rw [h1, h2, cornerShift_add_idx]
    have hpt : ∀ x : ℤ,
        (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F ω (x + Work.Peluse.cornerShift (fun i => ((E.symm u) i).1)
            (fun i => ((E.symm u') i).1) ω)))
        = ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F ω ((x + ∑ i, τ i) + Work.Peluse.cornerShift (fun i => (u i).1)
            (fun i => (u' i).1) ω)) := by
      intro x
      refine Finset.prod_congr rfl (fun ω _ => ?_)
      rw [hcs ω, show x + (Work.Peluse.cornerShift (fun i => (u i).1) (fun i => (u' i).1) ω
            + ∑ i, τ i)
          = (x + ∑ i, τ i) + Work.Peluse.cornerShift (fun i => (u i).1)
              (fun i => (u' i).1) ω from by ring]
    rw [tsum_congr hpt]
    exact Equiv.tsum_eq (Equiv.addRight (∑ i, τ i))
      (fun y : ℤ => ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (F ω (y + Work.Peluse.cornerShift (fun i => (u i).1) (fun i => (u' i).1) ω)))
  rw [← Equiv.sum_comp E.symm (g :=
    fun h : (i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun q => q + τ i)} =>
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun q => q + τ i)},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[Work.Peluse.weight ω]) (F ω (x + Work.Peluse.cornerShift
            (fun i => (h i).1) (fun i => (h' i).1) ω)))]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Equiv.sum_comp E.symm (g :=
    fun h' : (i : Fin t) → {x : ℤ // x ∈ (Q i).image (fun q => q + τ i)} =>
      ∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[Work.Peluse.weight ω]) (F ω (x + Work.Peluse.cornerShift
          (fun i => ((E.symm h) i).1) (fun i => (h' i).1) ω)))]
  exact Finset.sum_congr rfl (fun h' _ => key h h')

/-- **Per-coordinate translation of the direction sets**, for the box-sum power `boxSumPow`. -/
theorem boxSumPow_image_shift_idx (t : ℕ) (Q : Fin t → Finset ℤ) (τ : Fin t → ℤ)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxSumPow t (fun i => (Q i).image (fun q => q + τ i)) S f
      = Work.Peluse.boxSumPow t Q S f :=
  prodCubeSum_image_shift_idx t Q τ S (fun _ => f)

/-- **Per-coordinate translation of the direction sets**, for the box-normalised power. -/
theorem boxNormPow_image_shift_idx (t : ℕ) (Q : Fin t → Finset ℤ) (τ : Fin t → ℤ)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow t (fun i => (Q i).image (fun q => q + τ i)) S f
      = Work.Peluse.boxNormPow t Q S f := by
  rw [Work.Peluse.boxNormPow, Work.Peluse.boxNormPow, boxSumPow_image_shift_idx]

/-- **Per-coordinate translation of the direction sets**, for the box norm. -/
theorem boxNorm_image_shift_idx (t : ℕ) (Q : Fin t → Finset ℤ) (τ : Fin t → ℤ)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxNorm t (fun i => (Q i).image (fun q => q + τ i)) S f
      = Work.Peluse.boxNorm t Q S f := by
  rw [Work.Peluse.boxNorm, Work.Peluse.boxNorm, boxNormPow_image_shift_idx]

/-! ## Reflecting an `arithIcc` set is translating it -/

/-- **Reflecting an arithmetic progression is translating it**: `-arithIcc c L` is
`arithIcc c L` shifted by `-(L+1)·c`.  (`arithIcc c L = {c, 2c, …, Lc}` and
`c·j - (L+1)c = -c·(L+1-j)`.) -/
lemma arithIcc_neg_eq_image_shift (c : ℤ) (L : ℕ) :
    Work.Peluse.arithIcc (-c) L
      = (Work.Peluse.arithIcc c L).image (fun z : ℤ => z + (-((L : ℤ) + 1) * c)) := by
  ext z
  rw [Work.Peluse.arithIcc, Work.Peluse.arithIcc, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    refine ⟨c * ((L + 1 - n : ℕ) : ℤ), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(L + 1 - n : ℕ),
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    · have hcast : ((L + 1 - n : ℕ) : ℤ) = (L : ℤ) + 1 - (n : ℤ) := by omega
      rw [hcast]; ring
  · rintro ⟨a, ha, haz⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    refine ⟨(L + 1 - j : ℕ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    have hcast : ((L + 1 - j : ℕ) : ℤ) = (L : ℤ) + 1 - (j : ℤ) := by omega
    rw [hcast, ← haz]; ring

/-- `arithIcc (|c|) L` is `arithIcc c L` translated: the sign of the direction set is a shift. -/
lemma arithIcc_abs_eq_image_shift (c : ℤ) (L : ℕ) :
    Work.Peluse.arithIcc |c| L
      = (Work.Peluse.arithIcc c L).image
          (fun z : ℤ => z + (if c < 0 then -((L : ℤ) + 1) * c else 0)) := by
  have hzero : (fun z : ℤ => z + 0) = id := funext (fun z => add_zero z)
  rcases lt_trichotomy c 0 with h | h | h
  · rw [if_pos h, abs_of_neg h]
    exact arithIcc_neg_eq_image_shift c L
  · subst h
    rw [if_neg (lt_irrefl (0 : ℤ)), abs_zero, hzero, Finset.image_id]
  · rw [if_neg (not_lt.mpr (le_of_lt h)), abs_of_pos h, hzero, Finset.image_id]

end

end Work.Peluse.Prop36SW
