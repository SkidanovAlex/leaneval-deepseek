import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.cohom_mk

/-!
# The loop classes of the decorated letters of the `ℤ`-cover

Definitions and the basic telescoping identity used by the proof of
`Work.OROneRel.magnus_step_root_no_eps_zero`.

Let `c : α → ℤ` be a weight function and let `W : ℤ → FreeGroup α` be a *gauge*, i.e. `W i` is the
word attached to the level `i`.  The decorated word `decor c 0 (wordOf u)` is a list of symbols
`((a,i),b)`; each symbol stands for an edge of the `ℤ`-cover of the presentation complex of
`⟨α | u ^ l⟩` going from the level `coverSrc c p` to the level `coverTgt c p`, and its *loop class*
in the covering group is `W (coverSrc c p) * coverLetter p * (W (coverTgt c p))⁻¹`.

`gaugeMap W c` is the induced homomorphism `F (α × ℤ) →* F α` on the symbols of the rewriting, and
`gauge_decor` is the telescoping identity

  `gaugeMap W c (mk (decor c i L)) = W i * mk L * (W (i + lsig c L))⁻¹`,

whose specialisation `gauge_decor_zero` (`i = 0`, `L = wordOf u`, `cohom c u = 1`) reads

  `gaugeMap W c (mk (decor c 0 (wordOf u))) = u`,

i.e. the product of the loop classes of the decorated letters of `u` is `u` itself.  Consequently
the one-relator group `⟨β | v ^ l⟩` with `β` the decorated letters of non-trivial loop class and `v`
the word they spell maps into `⟨α | u ^ l⟩` sending `v ^ l` to `u ^ l = 1`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The source level of a decorated letter: for a positive letter the running weight read so far,
for a negative letter the running weight after the letter. -/
def coverSrc (c : α → ℤ) (p : (α × ℤ) × Bool) : ℤ :=
  if p.2 then p.1.2 else p.1.2 + c p.1.1

/-- The target level of a decorated letter. -/
def coverTgt (c : α → ℤ) (p : (α × ℤ) × Bool) : ℤ :=
  if p.2 then p.1.2 + c p.1.1 else p.1.2

/-- The generator of `F α` read at a decorated letter. -/
def coverLetter (p : (α × ℤ) × Bool) : FreeGroup α :=
  if p.2 then FreeGroup.of p.1.1 else (FreeGroup.of p.1.1)⁻¹

/-- The gauge map: the symbol `(a, i)` is sent to the loop class `W i * a * (W (i + c a))⁻¹` of the
edge from level `i` to level `i + c a`. -/
noncomputable def gaugeMap (W : ℤ → FreeGroup α) (c : α → ℤ) : FreeGroup (α × ℤ) →* FreeGroup α :=
  FreeGroup.lift fun p => W p.2 * FreeGroup.of p.1 * (W (p.2 + c p.1))⁻¹

@[simp] theorem gaugeMap_of (W : ℤ → FreeGroup α) (c : α → ℤ) (p : α × ℤ) :
    gaugeMap W c (FreeGroup.of p) = W p.2 * FreeGroup.of p.1 * (W (p.2 + c p.1))⁻¹ :=
  FreeGroup.lift_apply_of

/-- The loop class of a decorated letter, in terms of the gauge. -/
theorem gauge_letter (W : ℤ → FreeGroup α) (c : α → ℤ) (p : (α × ℤ) × Bool) :
    gaugeMap W c (if p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) =
      W (coverSrc c p) * coverLetter p * (W (coverTgt c p))⁻¹ := by
  obtain ⟨⟨a, i⟩, b⟩ := p
  cases b
  · -- negative letter
    simp only [Bool.false_eq_true, if_false]
    rw [map_inv, gaugeMap_of]
    simp only [coverSrc, coverTgt, coverLetter, Bool.false_eq_true, if_false, if_true]
    group
  · -- positive letter
    simp only [if_true]
    rw [gaugeMap_of]
    simp only [coverSrc, coverTgt, coverLetter, if_true]

private theorem mk_nil {β : Type*} : FreeGroup.mk ([] : List (β × Bool)) = 1 := rfl

private theorem mk_cons_true {β : Type*} (p : β) (M : List (β × Bool)) :
    FreeGroup.mk ((p, true) :: M) = FreeGroup.of p * FreeGroup.mk M := by
  rw [FreeGroup.of, FreeGroup.mul_mk]
  rfl

private theorem mk_cons_false {β : Type*} (p : β) (M : List (β × Bool)) :
    FreeGroup.mk ((p, false) :: M) = (FreeGroup.of p)⁻¹ * FreeGroup.mk M := by
  rw [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk]
  rfl

private theorem lsig_cons_true (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, true) :: L) = c a + lsig c L := rfl

private theorem lsig_cons_false (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, false) :: L) = -c a + lsig c L := rfl

/-- **Telescoping of the gauge map over a decorated word.**  The images of the decorated letters of
`L` (started at running weight `i`) multiply to `W i * (the word) * (W (i + weight))⁻¹`. -/
theorem gauge_decor (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    gaugeMap W c (FreeGroup.mk (decor c i L)) =
      W i * FreeGroup.mk L * (W (i + lsig c L))⁻¹ := by
  induction L generalizing i with
  | nil =>
      rw [show decor c i ([] : List (α × Bool)) = [] from rfl, lsig, List.map_nil, List.sum_nil]
      simp only [mk_nil, map_one, mul_one]
      rw [show i + 0 = i from by ring, mul_inv_cancel]
  | cons p L ih =>
      obtain ⟨a, b⟩ := p
      cases b
      · -- negative letter
        rw [show decor c i ((a, false) :: L) =
              ((a, i - c a), false) :: decor c (i - c a) L from rfl]
        simp only [mk_cons_false]
        rw [map_mul, map_inv, gaugeMap_of, ih (i - c a), lsig_cons_false]
        rw [show (i - c a) + c a = i from by ring]
        simp only [mk_cons_false]
        group
      · -- positive letter
        rw [show decor c i ((a, true) :: L) =
              ((a, i), true) :: decor c (i + c a) L from rfl]
        simp only [mk_cons_true]
        rw [map_mul, gaugeMap_of, ih (i + c a), lsig_cons_true]
        simp only [mk_cons_true]
        group

/-- **The base of the Magnus decomposition maps into `⟨α | u ^ l⟩`.**  If the total weight of `u`
vanishes then the product of the loop classes of the decorated letters of `u` is `u` itself. -/
theorem gauge_decor_zero (W : ℤ → FreeGroup α) (hW : W 0 = 1) {c : α → ℤ} {u : FreeGroup α}
    (hu : cohom c u = 1) :
    gaugeMap W c (FreeGroup.mk (decor c 0 (wordOf u))) = u := by
  have hlsig : lsig c (wordOf u) = 0 := by
    have h1 : cohom c (FreeGroup.mk (wordOf u)) = Multiplicative.ofAdd (lsig c (wordOf u)) :=
      cohom_mk c (wordOf u)
    rw [mk_wordOf] at h1
    have h2 : Multiplicative.ofAdd (lsig c (wordOf u)) = (1 : Multiplicative ℤ) := by
      rw [← h1]; exact hu
    exact Multiplicative.ofAdd.injective (by simpa using h2)
  rw [gauge_decor]
  simp only [hlsig, mk_wordOf, hW, zero_add, one_mul, inv_one, mul_one]

end Work.OROneRel
