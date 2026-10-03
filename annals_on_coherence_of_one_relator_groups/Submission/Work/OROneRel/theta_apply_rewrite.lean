/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The rewriting identity for the HNN step of the Freiheitssatz

`theta_apply_rewrite` computes the map `θ : ⟨α | r⟩ →* HNNExtension G' A B φ` of the HNN step
(`HNNStep.lean`) on a class `w` whose exponent sum in `t` vanishes and which does not involve the
distinguished letter `x`:

  `d.theta (mk w) = hnnOf r t (mk (magRewRel t w))`,

i.e. `θ` carries the class of `w` to the class of the Magnus rewriting `magRewRel t w` of `w` in the
base group `G' = ⟨(α \ {t}) × ℤ | magRewRel t r⟩`.

The proof has two halves.

* *Telescoping.*  If `σ_t L = 0` then `mk L = expand t (rewrite t L)` (`telescoping`), which, using
  `zeta t (mk v) = expand t v`, exhibits `w` as a product of the conjugates `t ^ i * s * t ^ (-i)`
  of the generators `s ≠ t` recorded by the rewriting.  Concretely `w = zeta t (magRewRel t w)`.

* *Conjugation.*  `θ` sends the generator `t` to the stable letter `τ` and a generator `s ≠ t` to the
  base generator `(s, 0)`, so on `t ^ i * s * t ^ (-i)` it produces `τ ^ i * (s,0) * τ ^ (-i)`; the
  field `conj` of `HNNStepCore` says that conjugating `(s, i)` by `τ` raises the index by one, so
  `τ ^ i * (s,0) * τ ^ (-i) = (s, i)`.  That is exactly the value of the base word `magRewRel t w`;
  here one uses `x ∉ relatorLetters w`, which guarantees that no index-decorated `x`-letter occurs,
  i.e. that the rewrite only involves generators to which `conj` applies.
-/
import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.mk_eq_expand_rewriteAux
import Submission.Work.OROneRel.rewrite_mem_letter
import Submission.Work.OROneRel.rewrite_isReduced
import Submission.Work.OROneRel.zeta_mk_eq_expand
import Submission.Work.OROneRel.sigma_mk

namespace Work.OROneRel

universe u

/-! ## Auxiliary lemmas -/

/-- Iteration of a conjugation-and-shift relation: if `τ * g k * τ⁻¹ = g (k+1)` for all `k : ℤ`,
then `τ ^ k * g 0 * τ ^ (-k) = g k` for all `k : ℤ` (both directions of the shift are available). -/
lemma theta_apply_rewrite_zpow_conj {G : Type*} [Group G] (τ : G) (g : ℤ → G)
    (hstep : ∀ k : ℤ, τ * g k * τ⁻¹ = g (k + 1)) (k : ℤ) :
    τ ^ k * g 0 * τ ^ (-k) = g k := by
  have key : ∀ n : ℕ,
      τ ^ (n : ℤ) * g 0 * τ ^ (-(n : ℤ)) = g (n : ℤ) ∧
      τ ^ (-(n : ℤ)) * g 0 * τ ^ (n : ℤ) = g (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · show τ ^ ((m : ℤ) + 1) * g 0 * τ ^ (-((m : ℤ) + 1)) = g ((m : ℤ) + 1)
        calc τ ^ ((m : ℤ) + 1) * g 0 * τ ^ (-((m : ℤ) + 1))
            = τ * (τ ^ (m : ℤ) * g 0 * τ ^ (-(m : ℤ))) * τ⁻¹ := by group
          _ = τ * g (m : ℤ) * τ⁻¹ := by rw [h1]
          _ = g ((m : ℤ) + 1) := hstep (m : ℤ)
      · show τ ^ (-((m : ℤ) + 1)) * g 0 * τ ^ ((m : ℤ) + 1) = g (-((m : ℤ) + 1))
        have hh := hstep (-(m : ℤ) - 1)
        rw [show (-(m : ℤ) - 1) + 1 = -(m : ℤ) from by ring] at hh
        calc τ ^ (-((m : ℤ) + 1)) * g 0 * τ ^ ((m : ℤ) + 1)
            = τ⁻¹ * (τ ^ (-(m : ℤ)) * g 0 * τ ^ (m : ℤ)) * τ := by group
          _ = τ⁻¹ * g (-(m : ℤ)) * τ := by rw [h2]
          _ = g (-((m : ℤ) + 1)) := by rw [← hh]; group
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · rw [hn]; exact (key n).1
  · rw [hn]; simpa using (key n).2

/-- The Magnus rewriting of a word introduces no new letters: every letter of `rewriteAux t i L` is
the decoration of a letter of `L`. -/
lemma theta_apply_rewrite_mem_rewriteAux {α : Type u} (t : α) (i : ℤ) :
    ∀ {L : List (α × Bool)} {p : ({a : α // a ≠ t} × ℤ) × Bool},
      p ∈ rewriteAux t i L → ((p.1.1 : α), p.2) ∈ L := by
  intro L
  induction L generalizing i with
  | nil => intro p hp; simp [rewriteAux] at hp
  | cons q L' ih =>
      intro p hp
      by_cases hq : q.1 = t
      · rw [rewriteAux_cons_of_eq t i L' hq] at hp
        exact List.mem_cons_of_mem _ (ih (i + (if q.2 then 1 else -1)) hp)
      · rw [rewriteAux_cons_of_ne t i L' hq] at hp
        rcases List.mem_cons.mp hp with h | h
        · rw [h]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih i h)

/-- The exponent sum in `t` of a word vanishes whenever the image of the word in the free group has
`σ_t = 1`. -/
lemma theta_apply_rewrite_sigmaList_eq_zero {α : Type u} {t : α} {L : List (α × Bool)}
    (h : sigma t (FreeGroup.mk L) = 1) : sigmaList t L = 0 := by
  have hm := sigma_mk t L
  rw [h] at hm
  simpa using hm.symm

/-- **Telescoping.**  If the exponent sum in `t` of the word `L` is zero, the `t`-letters dropped by
the Magnus rewriting reappear as the frame corrections of the conjugates recording the other
letters: `mk L = expand t (rewrite t L)`. -/
lemma theta_apply_rewrite_mk_eq_zeta {α : Type u} {t : α} {L : List (α × Bool)}
    (hL : sigmaList t L = 0) :
    FreeGroup.mk L = zeta t (FreeGroup.mk (rewrite t L)) := by
  have hmain := mk_eq_expand_rewriteAux t 0 L
  rw [hL] at hmain
  simp only [add_zero, zpow_zero, one_mul, mul_one] at hmain
  rw [hmain, zeta_mk_eq_expand t (rewrite t L)]
  rfl

/-- A letter `x` that does not occur in `L` does not occur in the Magnus rewriting of `L` either. -/
lemma theta_apply_rewrite_not_mem_letters {α : Type u} {t x : α} {L : List (α × Bool)}
    (hxL : ∀ b, (x, b) ∉ L) : ∀ p ∈ rewrite t L, (p.1.1 : α) ≠ x := by
  intro p hp hpx
  exact hxL p.2 (by rw [← hpx]; exact theta_apply_rewrite_mem_rewriteAux t 0 hp)

/-- Conjugation by the stable letter shifts the index of a base generator `(s, i)` with `s ≠ x`, for
all integers `i`. -/
lemma theta_apply_rewrite_conj_iterate {α : Type u} {r : FreeGroup α} {t x : α} {i j : ℤ}
    (d : HNNStepCore r t x i j) (s : {a : α // a ≠ t}) (hsx : (s : α) ≠ x) (k : ℤ) :
    hnnT r t d.A d.B d.phi ^ k * hnnOf r t (PresentedGroup.of (s, (0 : ℤ))) *
      hnnT r t d.A d.B d.phi ^ (-k) = hnnOf r t (PresentedGroup.of (s, k)) := by
  have hstep : ∀ k : ℤ, hnnT r t d.A d.B d.phi * hnnOf r t (PresentedGroup.of (s, k)) *
      (hnnT r t d.A d.B d.phi)⁻¹ = hnnOf r t (PresentedGroup.of (s, k + 1)) := by
    intro k
    simpa using d.conj (s : α) s.2 hsx k
  exact theta_apply_rewrite_zpow_conj (hnnT r t d.A d.B d.phi)
    (fun k => hnnOf r t (PresentedGroup.of (s, k))) hstep k

/-- `θ` on the conjugate `t ^ i * s * t ^ (-i)`, for `s ≠ x`: it is the base generator `(s, i)`. -/
lemma theta_apply_rewrite_gen {α : Type u} {r : FreeGroup α} {t x : α} {i j : ℤ}
    (d : HNNStepCore r t x i j) (q : ({a : α // a ≠ t} × ℤ)) (hqx : (q.1 : α) ≠ x) :
    d.theta (PresentedGroup.mk ({r} : Set (FreeGroup α)) (zeta t (FreeGroup.of q))) =
      hnnOf r t (PresentedGroup.of q) := by
  rw [show zeta t (FreeGroup.of q) =
      (FreeGroup.of t) ^ q.2 * FreeGroup.of (q.1 : α) * (FreeGroup.of t) ^ (-(q.2)) from by
    simp only [zeta, FreeGroup.lift_apply_of]]
  simp only [map_mul, map_zpow]
  rw [show (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.of t)) =
        PresentedGroup.of t from rfl,
      d.theta_t,
      show (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.of (q.1 : α))) =
        PresentedGroup.of (q.1 : α) from rfl,
      d.theta_of (q.1 : α) q.1.2]
  exact theta_apply_rewrite_conj_iterate d q.1 hqx q.2

/-- `θ` carries the expansion of a decorated word `v` (whose letters avoid `x`) to the class of `v`
in the base group. -/
lemma theta_apply_rewrite_list {α : Type u} {r : FreeGroup α} {t x : α} {i j : ℤ}
    (d : HNNStepCore r t x i j) :
    ∀ v : List (({a : α // a ≠ t} × ℤ) × Bool),
      (∀ p ∈ v, (p.1.1 : α) ≠ x) →
      d.theta (PresentedGroup.mk ({r} : Set (FreeGroup α)) (zeta t (FreeGroup.mk v))) =
        hnnOf r t (PresentedGroup.mk ({magRewRel t r} : Set (FreeGroup ({a : α // a ≠ t} × ℤ)))
          (FreeGroup.mk v)) := by
  intro v
  induction v with
  | nil =>
      intro _
      rw [show FreeGroup.mk ([] : List (({a : α // a ≠ t} × ℤ) × Bool)) = 1 from
        FreeGroup.one_eq_mk.symm]
      simp
  | cons p v' ih =>
      intro hv
      have hp : (p.1.1 : α) ≠ x := hv p (List.mem_cons_self ..)
      have hv' : ∀ q ∈ v', (q.1.1 : α) ≠ x := fun q hq => hv q (List.mem_cons_of_mem p hq)
      rw [mk_cons_aux p v']
      simp only [map_mul, map_zpow]
      rw [theta_apply_rewrite_gen d p.1 hp, ih hv']
      rfl

/-! ## The rewriting identity -/

theorem theta_apply_rewrite {α : Type u} {r : FreeGroup α} {t x : α} {i j : ℤ}
    (d : Work.OROneRel.HNNStepCore r t x i j) (w : FreeGroup α)
    (hsigma : Work.OROneRel.sigma t w = 1) (hxw : x ∉ Work.OROneRel.relatorLetters w) :
    d.theta (PresentedGroup.mk ({r} : Set (FreeGroup α)) w) =
      Work.OROneRel.hnnOf r t (PresentedGroup.mk
        ({Work.OROneRel.magRewRel t r} : Set (FreeGroup ({a : α // a ≠ t} × ℤ)))
        (Work.OROneRel.magRewRel t w)) := by
  classical
  have hL : sigmaList t w.toWord = 0 :=
    theta_apply_rewrite_sigmaList_eq_zero (L := w.toWord) (by rw [FreeGroup.mk_toWord]; exact hsigma)
  have hzeta : w = zeta t (magRewRel t w) := by
    have h := theta_apply_rewrite_mk_eq_zeta (t := t) (L := w.toWord) hL
    rwa [FreeGroup.mk_toWord] at h
  have hnoX : ∀ p ∈ rewrite t w.toWord, (p.1.1 : α) ≠ x :=
    theta_apply_rewrite_not_mem_letters (t := t) (x := x) (L := w.toWord)
      (fun b hb => hxw ⟨b, hb⟩)
  have key := theta_apply_rewrite_list d (rewrite t w.toWord) hnoX
  calc d.theta (PresentedGroup.mk ({r} : Set (FreeGroup α)) w)
      = d.theta (PresentedGroup.mk ({r} : Set (FreeGroup α)) (zeta t (magRewRel t w))) :=
        congrArg d.theta (congrArg (PresentedGroup.mk ({r} : Set (FreeGroup α))) hzeta)
    _ = Work.OROneRel.hnnOf r t (PresentedGroup.mk
          ({Work.OROneRel.magRewRel t r} : Set (FreeGroup ({a : α // a ≠ t} × ℤ)))
          (Work.OROneRel.magRewRel t w)) := key

end Work.OROneRel
