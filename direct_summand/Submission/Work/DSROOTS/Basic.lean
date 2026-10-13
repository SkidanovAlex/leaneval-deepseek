import Submission.Work.DSMap.Mix2

/-!
# DSROOTS — `p`-power roots of finitely many elements by iterated André

Foundations of the `ROOTS` node of the MIX2 route (`direct_summand_mix2.md`, node
`area_ROOTS`): given a perfectoid ring `W` (with its `ϖ`-tower) and finitely many elements
`t i`, there is a perfectoid extension `W →* W'` with the same `ϖ`, faithfully flat modulo
`p`, in which every `t i` has a compatible system of `p`-power roots
(`tr i 0 = t i`, `(tr i (k+1))^p = tr i k`).

The route is: apply André's lemma (`DSMap.Mix.area_M2'`) once per element, and compose;
faithful flatness modulo `p` is stable under composition, which is the point of the
ring-hom-level formulation `FFp` below.

## Main definitions

* `Work.DSROOTS.quotMap p f` — the induced map `R ⧸ (p) →+* S ⧸ (p)`.
* `Work.DSROOTS.FFp p f` — `f` is faithfully flat modulo `p`, i.e. `quotMap p f` is
  faithfully flat (`RingHom.FaithfullyFlat`).  It composes definitionally (`FFp.comp`).
* `Work.DSROOTS.IsPRoot p s tr` — `tr` is a compatible system of `p`-power roots of `s`.
* `Work.DSROOTS.AndreStep p` — one application of André's lemma, in root-system form.
* `Work.DSROOTS.RootExt p W Q t L` — data of the iterated André extension, with root
  systems for the elements of `L`.

## Main results

* `Work.DSROOTS.FFp.comp` — composition.
* `Work.DSROOTS.FFp.iff` — bridge to the `Module.FaithfullyFlat` form used by the frozen
  node statements (and by `area_M2'`).
* `Work.DSROOTS.andreStep_of_M2` (in `Work.DSROOTS.andreStep_of_M2`) — André's lemma
  (`DSMap.Mix.area_M2'`) gives `AndreStep`.
* `Work.DSROOTS.RootExt.list`, `Work.DSROOTS.exists_roots_of_andreStep` (in
  `Work.DSROOTS.RootExt`).
* `DSMap.Mix2.area_ROOTS_proved` (in `Submission/Work/DSROOTS/Main.lean`) — the frozen
  `area_ROOTS` statement (and the axiom-clean conditional form
  `DSMap.Mix2.area_ROOTS_of_andreStep`).
-/

set_option linter.style.haveILetI false

universe a

namespace Work.DSROOTS

open DSMap DSMap.Mix

/-! ## 1. Faithfully flat modulo `p` -/

/-- The canonical map `R ⧸ (p) →+* S ⧸ (p)` induced by `f : R →+* S`. -/
def quotMap (p : ℕ) {R S : Type a} [CommRing R] [CommRing S] (f : R →+* S) :
    R ⧸ Ideal.span {(p : R)} →+* S ⧸ Ideal.span {(p : S)} :=
  Ideal.quotientMap (Ideal.span {(p : S)}) f (by
    rw [Ideal.span_le]
    rintro x (rfl : x = (p : R))
    change f (p : R) ∈ Ideal.span {(p : S)}
    rw [map_natCast]
    exact Ideal.subset_span rfl)

/-- `f : R →+* S` is **faithfully flat modulo `p`**: the induced map of quotients
`R ⧸ (p) →+* S ⧸ (p)` is faithfully flat. -/
def FFp (p : ℕ) {R S : Type a} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  (quotMap p f).FaithfullyFlat

/-- The canonical identification `S ⧸ (p) ≃+* S ⧸ (p).map f` (the two ideals coincide, since
`f p = p`). -/
def quotIso (p : ℕ) {R S : Type a} [CommRing R] [CommRing S] (f : R →+* S) :
    (S ⧸ Ideal.span {(p : S)}) ≃+* (S ⧸ (Ideal.span {(p : R)}).map f) :=
  Ideal.quotientEquiv _ _ (RingEquiv.refl S) (by
    simp [Ideal.map_span, map_natCast])

@[simp]
theorem quotIso_apply (p : ℕ) {R S : Type a} [CommRing R] [CommRing S] (f : R →+* S) (s : S) :
    quotIso p f (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ s := rfl

theorem quotMap_mk (p : ℕ) {R S : Type a} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    quotMap p f (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (f r) :=
  Ideal.quotientMap_mk

theorem quotMap_id (p : ℕ) {R : Type a} [CommRing R] :
    quotMap p (RingHom.id R) = RingHom.id (R ⧸ Ideal.span {(p : R)}) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [quotMap_mk]

theorem quotMap_comp (p : ℕ) {R S T : Type a} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    quotMap p (g.comp f) = (quotMap p g).comp (quotMap p f) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [quotMap_mk, RingHom.comp_apply]

namespace FFp

theorem id (p : ℕ) {R : Type a} [CommRing R] : FFp p (RingHom.id R) := by
  rw [FFp, quotMap_id]
  exact RingHom.FaithfullyFlat.of_bijective (f := RingHom.id (R ⧸ Ideal.span {(p : R)}))
    Function.bijective_id

/-- Faithful flatness modulo `p` is stable under composition. -/
theorem comp (p : ℕ) {R S T : Type a} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h₁ : FFp p f) (h₂ : FFp p g) : FFp p (g.comp f) := by
  rw [FFp, quotMap_comp]
  exact RingHom.FaithfullyFlat.stableUnderComposition (quotMap p f) (quotMap p g) h₁ h₂

end FFp

/-- Bridge between `FFp` (ring-hom form, convenient for composition) and the
`Module.FaithfullyFlat` form used by the frozen node statements. -/
theorem FFp.iff (p : ℕ) {R S : Type a} [CommRing R] [CommRing S] [Algebra R S] :
    FFp p (algebraMap R S) ↔
      Module.FaithfullyFlat (R ⧸ Ideal.span {(p : R)})
        (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S)) := by
  have key : ((quotIso p (algebraMap R S) :
        (S ⧸ Ideal.span {(p : S)}) →+* (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S))).comp
        (quotMap p (algebraMap R S))) =
      algebraMap (R ⧸ Ideal.span {(p : R)}) (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S)) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.comp_apply, quotMap_mk]
    show quotIso p (algebraMap R S) (Ideal.Quotient.mk _ ((algebraMap R S) r)) =
      (algebraMap (R ⧸ Ideal.span {(p : R)}) (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S)))
        (Ideal.Quotient.mk _ r)
    rw [quotIso_apply]
    exact (Ideal.quotientMap_mk (f := algebraMap R S) (H := le_rfl) (x := r)).symm
  have isoFF : (quotIso p (algebraMap R S) :
      (S ⧸ Ideal.span {(p : S)}) →+* (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S))).FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective (quotIso p (algebraMap R S)).bijective
  have isoFF' : ((quotIso p (algebraMap R S)).symm :
      (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S)) →+* (S ⧸ Ideal.span {(p : S)})).FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective (quotIso p (algebraMap R S)).symm.bijective
  constructor
  · intro h
    have h₂ := RingHom.FaithfullyFlat.stableUnderComposition (quotMap p (algebraMap R S))
      (quotIso p (algebraMap R S) :
        (S ⧸ Ideal.span {(p : S)}) →+* (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S))) h isoFF
    exact (RingHom.faithfullyFlat_algebraMap_iff (R := R ⧸ Ideal.span {(p : R)})
      (S := S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S))).mp (by rw [← key]; exact h₂)
  · intro h
    have h₁ : (algebraMap (R ⧸ Ideal.span {(p : R)})
        (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S))).FaithfullyFlat :=
      (RingHom.faithfullyFlat_algebraMap_iff (R := R ⧸ Ideal.span {(p : R)})
        (S := S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S))).mpr h
    have h₂ : ((quotIso p (algebraMap R S) :
        (S ⧸ Ideal.span {(p : S)}) →+* (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S))).comp
        (quotMap p (algebraMap R S))).FaithfullyFlat := by
      rw [key]; exact h₁
    have h₃ := RingHom.FaithfullyFlat.stableUnderComposition
      ((quotIso p (algebraMap R S) :
        (S ⧸ Ideal.span {(p : S)}) →+* (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S))).comp
        (quotMap p (algebraMap R S)))
      ((quotIso p (algebraMap R S)).symm :
        (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S)) →+* (S ⧸ Ideal.span {(p : S)})) h₂ isoFF'
    have h₄ : ((quotIso p (algebraMap R S)).symm :
          (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S)) →+* (S ⧸ Ideal.span {(p : S)})).comp
        ((quotIso p (algebraMap R S) :
          (S ⧸ Ideal.span {(p : S)}) →+* (S ⧸ (Ideal.span {(p : R)}).map (algebraMap R S))).comp
          (quotMap p (algebraMap R S))) =
        quotMap p (algebraMap R S) := by
      rw [← RingHom.comp_assoc]
      simp
    rwa [h₄] at h₃

/-! ## 2. Compatible systems of `p`-power roots -/

/-- `tr` is a compatible system of `p`-power roots of `s`: `tr 0 = s` and
`tr (k+1) ^ p = tr k`.  Thus `tr k` is a `p ^ k`-th root of `s` (`IsPRoot.pow`). -/
def IsPRoot (p : ℕ) {W : Type a} [CommRing W] (s : W) (tr : ℕ → W) : Prop :=
  tr 0 = s ∧ ∀ k : ℕ, (tr (k + 1)) ^ p = tr k

namespace IsPRoot

theorem of_root {p : ℕ} {W : Type a} [CommRing W] {s : W} {tr : ℕ → W}
    (h₀ : tr 0 = s) (h : ∀ k : ℕ, (tr (k + 1)) ^ p = tr k) : IsPRoot p s tr :=
  ⟨h₀, h⟩

theorem zero {p : ℕ} {W : Type a} [CommRing W] {s : W} {tr : ℕ → W} (h : IsPRoot p s tr) :
    tr 0 = s :=
  h.1

theorem succ {p : ℕ} {W : Type a} [CommRing W] {s : W} {tr : ℕ → W} (h : IsPRoot p s tr)
    (k : ℕ) : (tr (k + 1)) ^ p = tr k :=
  h.2 k

/-- The `k`-th element is a `p ^ k`-th root of `s`. -/
theorem pow {p : ℕ} {W : Type a} [CommRing W] {s : W} {tr : ℕ → W} (h : IsPRoot p s tr)
    (n : ℕ) : (tr n) ^ (p ^ n) = s := by
  induction n with
  | zero => simpa using h.1
  | succ n ih => rw [pow_succ, mul_comm (p ^ n) p, pow_mul, h.2 n, ih]

/-- Compatible systems of `p`-power roots push forward along ring homs. -/
theorem map {p : ℕ} {W W' : Type a} [CommRing W] [CommRing W'] {s : W} {tr : ℕ → W}
    (h : IsPRoot p s tr) (g : W →+* W') : IsPRoot p (g s) (fun k => g (tr k)) :=
  ⟨by simp [h.1], fun k => by rw [← map_pow, h.2 k]⟩

/-- Restriction of a root system: `tr (k + n)` is a root system of `tr n`. -/
theorem shift {p : ℕ} {W : Type a} [CommRing W] {s : W} {tr : ℕ → W} (h : IsPRoot p s tr)
    (n : ℕ) : IsPRoot p (tr n) (fun k => tr (k + n)) :=
  ⟨by simp, fun k => by simpa [Nat.add_right_comm] using h.2 (k + n)⟩

end IsPRoot

/-! ## 3. One step of André, in root-system form -/

/-- **One application of André's lemma**, in the form needed by `ROOTS`: for every perfectoid
`W` and every `s : W` there is a perfectoid extension `W →* W'` with the same `ϖ`, faithfully
flat modulo `p`, in which `s` has a compatible system of `p`-power roots.
(`Work.DSROOTS.andreStep_of_M2` obtains this from `DSMap.Mix.area_M2'`.) -/
def AndreStep (p : ℕ) : Prop :=
  ∀ (W : Type a) [CommRing W] (Q : PerfectoidData p W) (s : W),
    ∃ (W' : Type a) (_ : CommRing W') (g : W →+* W') (Q' : PerfectoidData p W'),
      (∀ k : ℕ, Q'.ϖ k = g (Q.ϖ k)) ∧ FFp p g ∧ ∃ tr : ℕ → W', IsPRoot p (g s) tr

end Work.DSROOTS
