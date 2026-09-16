import Mathlib
import Submission.ZagierHoffmanProof.StepL60
open scoped BigOperators

/-!
# Step L61: main2_case1_j1 sub-lemmas — S1 (guarded sum → subtype) committed

The CASE-1 j = 1 splice (main2_case1_j1) needs its hid sign-algebra in three
sub-lemmas (PLAN SESSION 205); this module commits S1:
  ★ sum_guarded_subtype (u f) :
      (∑ i : ι, (if i = u then 0 else f i)) = ∑ i : {i : ι // i ≠ u}, f i
    — the guarded type-1 sum (0 at the leading a-index u) is the sum over the
    subtype {i₀ ≠ u}.  Proof: split the full sum at u (Finset.sum_erase_add; the
    u-summand is 0; erase-summands simplify by x ≠ u — note Finset.mem_erase.mp's
    conjunction is ordered (x ≠ u) ∧ (x ∈ univ) here, use `.1`) and bridge the
    erase-Finset sum to the subtype sum (Finset.sum_subtype with an EXPLICIT
    filter-based Fintype instance — the subtype {i // i ≠ u} has no synthesizable
    Fintype in this Mathlib, so the instance is built by Fintype.subtype
    (s := univ.filter (· ≠ u)) (by intro x; simp [Finset.mem_filter]) and passed
    with @-application; identical at the statement-level letI and in the proof).
This is the permanent generic bridge every later guarded sum in the project needs.
NEXT: S2 (neg of the member sums: Finset.sum_neg_distrib + ratFunc_coe_neg) and S3
(folding ζ + A + B + C = 0 into the three-family signed identity), then
main2_case1_j1.  Named gates unchanged: j=0 G5 chains, m≥3 hierarchy, theorem_B/D.
-/

/-- ★ S1: the guarded sum (0 at u) equals the sum over the subtype {i ≠ u}. -/
lemma sum_guarded_subtype {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : Type} [AddCommMonoid M] (u : ι) (f : ι → M) :
    letI : Fintype {i : ι // i ≠ u} :=
      Fintype.subtype ((Finset.univ : Finset ι).filter (fun i => i ≠ u))
        (by intro x; simp [Finset.mem_filter])
    (∑ i : ι, (if i = u then 0 else f i)) = ∑ i : {i : ι // i ≠ u}, f i := by
  classical
  let inst : Fintype {i : ι // i ≠ u} :=
    Fintype.subtype ((Finset.univ : Finset ι).filter (fun i => i ≠ u))
      (by intro x; simp [Finset.mem_filter])
  letI : Fintype {i : ι // i ≠ u} := inst
  -- half 1: guarded = erase
  let g : ι → M := fun i => if i = u then 0 else f i
  have hs := Finset.sum_erase_add (s := (Finset.univ : Finset ι)) (f := g) (a := u) (Finset.mem_univ u)
  have h2 : (∑ x ∈ (Finset.univ : Finset ι).erase u, g x) =
      ∑ x ∈ (Finset.univ : Finset ι).erase u, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
    simp [g, hxu]
  have h1 : (∑ i : ι, g i) = ∑ i ∈ (Finset.univ : Finset ι).erase u, f i := by
    rw [← hs]
    rw [h2]
    simp [g]
  -- half 2: erase = subtype
  have hfil : (Finset.univ : Finset ι).filter (fun i => i ≠ u) = (Finset.univ : Finset ι).erase u := by
    ext i
    simp
  have hsum : (∑ x ∈ (Finset.univ : Finset ι).filter (fun i => i ≠ u), f x) =
      ∑ x : {i : ι // i ≠ u}, f x := by
    exact @Finset.sum_subtype ι M _ (fun i : ι => i ≠ u) inst
      ((Finset.univ : Finset ι).filter (fun i => i ≠ u)) (by intro x; simp [Finset.mem_filter]) f
  calc
    (∑ i : ι, (if i = u then 0 else f i)) = ∑ i : ι, g i := by rfl
    _ = ∑ i ∈ (Finset.univ : Finset ι).erase u, f i := h1
    _ = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => i ≠ u), f i := by
          rw [hfil]
    _ = ∑ i : {i : ι // i ≠ u}, f i := hsum
