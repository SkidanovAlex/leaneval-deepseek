import Submission.Work.DSROOTS.Basic

/-!
# DSROOTS: iterated André extensions

The `ROOTS` node of the MIX2 route, as a reusable structure: `RootExt p W Q t L` is the data of
the extension of `W` obtained by applying André's lemma (`AndreStep`) once for each element of the
list `L`; it records the extension ring `W'`, the extension map `f : W →+* W'`, its perfectoid
data `Q'` (with the same `ϖ`-tower), faithful flatness modulo `p` (`FFp p f`), and a compatible
system of `p`-power roots of every `t i` with `i ∈ L`.

`StepData` is the same data for a single application of André's lemma, re-packaged as a structure
so that it can be used in `Type`-valued definitions (`AndreStep` is a `Prop`, so its content is
extracted with `Classical.choice`, cf. `stepData`).

The main outputs are

* `Work.DSROOTS.StepData`, `Work.DSROOTS.stepData` — one André step as data;
* `Work.DSROOTS.RootExt.nil`, `Work.DSROOTS.RootExt.cons` — the one-step API;
* `Work.DSROOTS.RootExt.list` — the iteration over a list;
* `Work.DSROOTS.exists_roots_of_andreStep` — the `ROOTS` statement in ring-hom form, from the
  one-step hypothesis alone (so it is axiom-free given `AndreStep`).
-/

set_option linter.style.haveILetI false

universe a

namespace Work.DSROOTS

open DSMap DSMap.Mix

/-- The data produced by one application of André's lemma to a perfectoid ring `(W, Q)` and an
element `s : W`: an extension ring `W'`, a map `f : W →+* W'`, perfectoid data `Q'` on `W'` with
the same `ϖ`-tower, faithful flatness modulo `p`, and a compatible `p`-power root system of `f s`. -/
structure StepData (p : ℕ) (W : Type a) [CommRing W] (Q : PerfectoidData p W) (s : W) where
  /-- the extension ring -/
  W' : Type a
  /-- the ring structure on the extension ring -/
  [commRing : CommRing W']
  /-- the extension map -/
  f : W →+* W'
  /-- perfectoid data on the extension -/
  Q' : PerfectoidData p W'
  /-- the chosen `ϖ`-towers agree -/
  varpi : ∀ k : ℕ, Q'.ϖ k = f (Q.ϖ k)
  /-- the extension is faithfully flat modulo `p` -/
  ff : FFp p f
  /-- a compatible `p`-power root system of `f s` -/
  tr : ℕ → W'
  /-- `tr` is a compatible system of `p`-power roots -/
  isRoot : IsPRoot p (f s) tr

/-- One application of the one-step hypothesis `h`, packaged as a structure. -/
noncomputable def stepData {p : ℕ} {W : Type a} [CommRing W] {Q : PerfectoidData p W}
    (h : AndreStep.{a} p) (s : W) : StepData p W Q s := by
  classical
  have hne : Nonempty (StepData p W Q s) := by
    obtain ⟨W', _, g, Q', hϖ, hff, tr, htr⟩ := h W Q s
    exact ⟨{ W' := W', f := g, Q' := Q', varpi := hϖ, ff := hff, tr := tr, isRoot := htr }⟩
  exact Classical.choice hne

/-- The data of the iterated André extension of `(W, Q)` along the list `L`: an extension ring
`W'`, an extension map `f : W →+* W'`, perfectoid data `Q'` on `W'` with the same `ϖ`-tower,
faithful flatness of `f` modulo `p`, and compatible `p`-power root systems for the elements
`t i`, `i ∈ L`. -/
structure RootExt (p : ℕ) (W : Type a) [CommRing W] (Q : PerfectoidData p W)
    {ι : Type a} (t : ι → W) (L : List ι) where
  /-- the extension ring -/
  W' : Type a
  /-- the ring structure on the extension ring -/
  [commRing : CommRing W']
  /-- the extension map -/
  f : W →+* W'
  /-- perfectoid data on the extension -/
  Q' : PerfectoidData p W'
  /-- the chosen `ϖ`-towers agree -/
  varpi : ∀ k : ℕ, Q'.ϖ k = f (Q.ϖ k)
  /-- the extension is faithfully flat modulo `p` -/
  ff : FFp p f
  /-- compatible `p`-power roots of the selected elements -/
  roots : ∀ i ∈ L, ∃ tr : ℕ → W', IsPRoot p (f (t i)) tr

namespace RootExt

/-- The trivial extension of the empty list. -/
def nil {p : ℕ} {W : Type a} [CommRing W] (Q : PerfectoidData p W)
    {ι : Type a} (t : ι → W) : RootExt p W Q t [] where
  W' := W
  f := RingHom.id W
  Q' := Q
  varpi := fun k => rfl
  ff := FFp.id p
  roots := by
    intro i hi
    simp at hi

/-- Extend the iteration by one more element: apply the one-step hypothesis `h` to the current
ring and push the previously obtained root systems forward. -/
noncomputable def cons {p : ℕ} {W : Type a} [CommRing W] {Q : PerfectoidData p W}
    {ι : Type a} {t : ι → W} {L : List ι} (R : RootExt p W Q t L) (h : AndreStep.{a} p) (a : ι) :
    RootExt p W Q t (a :: L) := by
  letI := R.commRing
  let S : StepData p R.W' R.Q' (R.f (t a)) := stepData h (R.f (t a))
  letI := S.commRing
  exact
    { W' := S.W'
      f := S.f.comp R.f
      Q' := S.Q'
      varpi := fun k => by rw [S.varpi k, R.varpi k]; rfl
      ff := FFp.comp p R.f S.f R.ff S.ff
      roots := by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hjL
        · exact ⟨S.tr, S.isRoot⟩
        · obtain ⟨tr, htr⟩ := R.roots j hjL
          exact ⟨fun k => S.f (tr k), htr.map S.f⟩ }

/-- The iteration over a list: apply the one-step hypothesis once per element. -/
noncomputable def list {p : ℕ} {W : Type a} [CommRing W] (Q : PerfectoidData p W)
    {ι : Type a} (t : ι → W) (h : AndreStep.{a} p) (L : List ι) : RootExt p W Q t L := by
  induction L with
  | nil => exact nil Q t
  | cons a L ih => exact ih.cons h a

end RootExt

/-- **`ROOTS` in ring-hom form**: from the one-step André hypothesis, compatible `p`-power roots
of *all* elements `t i` of a finite index type, after a perfectoid extension with the same
`ϖ`-tower which is faithfully flat modulo `p`. -/
theorem exists_roots_of_andreStep {p : ℕ} (h : AndreStep.{a} p) (W : Type a) [CommRing W]
    (Q : PerfectoidData p W) {ι : Type a} [Finite ι] (t : ι → W) :
    ∃ (W' : Type a) (_ : CommRing W') (f : W →+* W') (Q' : PerfectoidData p W'),
      (∀ k : ℕ, Q'.ϖ k = f (Q.ϖ k)) ∧ FFp p f ∧
        ∃ tr : ι → ℕ → W', ∀ i : ι, IsPRoot p (f (t i)) (tr i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let L : List ι := (Finset.univ : Finset ι).val.toList
  have hL : ∀ i : ι, i ∈ L := fun i =>
    Multiset.mem_toList.mpr (Finset.mem_val.mpr (Finset.mem_univ i))
  let R : RootExt p W Q t L := RootExt.list Q t h L
  choose tr htr using fun i : ι => R.roots i (hL i)
  exact ⟨R.W', R.commRing, R.f, R.Q', R.varpi, R.ff, tr, htr⟩

end Work.DSROOTS
