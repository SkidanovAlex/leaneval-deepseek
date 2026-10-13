/-
  Area E7: padding a `Stratum` by `d` coordinates pinned to zero.

  The target `Work.WilE7.pad_stratum` inserts, between the base coordinates `x ∈ ℝ^p` and the
  fibre coordinates `y ∈ ℝ^q` of a stratum `S : Stratum p q`, a block of `d` coordinates which
  are required to vanish.  Concretely

  * `midInj p d q : Fin (p+q) → Fin (p+(d+q))` is the injection which skips the inserted block
    `p, …, p+d-1`;
  * `pins p d q r` is the list of the `d` linear equations pinning the inserted coordinates to
    `0`;
  * `padStrat p q d X` is `X` extended along `midInj` with those equations adjoined;
  * `tidy X` removes repeated basic sets, so that the number of basic sets is controlled by the
    degree (which is what makes the degree bound of the target expressible as a polynomial in
    `S.X.deg`).

  Everything in this file is unconditional: no `Star`/`SubPf`/`Good` input is used.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE8.Extend
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE8.Extend.semipf_deg_extend

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The coordinate injection skipping the inserted block -/

/-- The value of the coordinate injection on the level of `ℕ`. -/
def midVal (p d : ℕ) (i : ℕ) : ℕ := if i < p then i else i + d

theorem midVal_injective (p d : ℕ) : Function.Injective (midVal p d) := by
  intro i j h
  simp only [midVal] at h
  split_ifs at h <;> omega

theorem midVal_lt {p d : ℕ} {i : ℕ} (h : i < p) : midVal p d i = i := by
  simp only [midVal, if_pos h]

theorem midVal_ge {p d : ℕ} {i : ℕ} (h : ¬ i < p) : midVal p d i = i + d := by
  simp only [midVal, if_neg h]

theorem midVal_lt_bound {p d q : ℕ} {i : ℕ} (h : i < p + q) : midVal p d i < p + (d + q) := by
  simp only [midVal]
  split_ifs <;> omega

/-- The injection `Fin (p+q) → Fin (p+(d+q))` which skips the `d` middle coordinates
`p, …, p+d-1`: it sends the base coordinates `Fin p` to themselves and the fibre coordinates
`Fin q` to their position after the inserted block. -/
def midInj (p d q : ℕ) : Fin (p + q) → Fin (p + (d + q)) :=
  fun i => ⟨midVal p d i, midVal_lt_bound i.isLt⟩

theorem midInj_injective (p d q : ℕ) : Function.Injective (midInj p d q) := by
  intro i j h
  have h' : midVal p d i = midVal p d j := congrArg Fin.val h
  exact Fin.ext (midVal_injective p d h')

theorem midInj_castAdd (p d q : ℕ) (a : Fin p) :
    midInj p d q (Fin.castAdd q a) = Fin.castAdd (d + q) a := by
  refine Fin.ext ?_
  exact midVal_lt a.isLt

theorem midInj_natAdd (p d q : ℕ) (b : Fin q) :
    midInj p d q (Fin.natAdd p b) = Fin.natAdd p (Fin.natAdd d b) := by
  refine Fin.ext ?_
  show midVal p d (p + b.val) = p + (d + b.val)
  rw [midVal_ge (by omega)]
  omega

/-- The position of the `a`-th inserted (pinned) coordinate. -/
def midIdx (p d q : ℕ) (a : Fin d) : Fin (p + (d + q)) := ⟨p + a.val, by omega⟩

theorem midIdx_eq_natAdd (p d q : ℕ) (a : Fin d) :
    midIdx p d q a = Fin.natAdd p (Fin.castAdd q a) := rfl

theorem midInj_ne_midIdx (p d q : ℕ) (i : Fin (p + q)) (a : Fin d) :
    midInj p d q i ≠ midIdx p d q a := by
  intro h
  have hv : midVal p d i.val = p + a.val := congrArg Fin.val h
  simp only [midVal] at hv
  split_ifs at hv <;> omega

/-! ## The pinning equations -/

/-- The linear polynomial pinning the `a`-th inserted coordinate to `0`. -/
@[reducible] def pinAt (p d q r : ℕ) (a : Fin d) : EAPoly (p + (d + q)) r :=
  MvPolynomial.X (Sum.inl (midIdx p d q a))

/-- The list of the `d` pinning equations. -/
def pins (p d q r : ℕ) : List (EAPoly (p + (d + q)) r) :=
  (List.finRange d).map (pinAt p d q r)

theorem mem_pins {p d q r : ℕ} {Q : EAPoly (p + (d + q)) r} :
    Q ∈ pins p d q r ↔ ∃ a : Fin d, Q = pinAt p d q r a := by
  simp only [pins, List.mem_map, List.mem_finRange]
  constructor
  · rintro ⟨a, -, rfl⟩; exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩; exact ⟨a, trivial, rfl⟩

theorem pins_length (p d q r : ℕ) : (pins p d q r).length = d := by
  simp [pins]

theorem pinAt_mem (p d q r : ℕ) (a : Fin d) : pinAt p d q r a ∈ pins p d q r :=
  mem_pins.mpr ⟨a, rfl⟩

theorem eaEval_pinAt {p d q r : ℕ} (c : EAChain (p + (d + q)) r) (a : Fin d)
    (z : Fin (p + (d + q)) → ℝ) :
    eaEval c (pinAt p d q r a) z = z (midIdx p d q a) := by
  simp only [pinAt, eaEval, MvPolynomial.eval_X, Sum.elim_inl]

/-! ## Adjoining a list of equations to every basic set -/

/-- Adjoin each of the equations `Qs` to every basic set of `X`, keeping the chain. -/
def addEqs {k : ℕ} (X : SemiPf k) (Qs : List (EAPoly k X.r)) : SemiPf k :=
  ⟨X.r, X.c, X.basics.map (fun B => (⟨B.eqs ++ Qs, B.pos⟩ : Basic k X.r))⟩

@[simp] theorem addEqs_r {k : ℕ} (X : SemiPf k) (Qs : List (EAPoly k X.r)) :
    (addEqs X Qs).r = X.r := rfl

@[simp] theorem addEqs_c {k : ℕ} (X : SemiPf k) (Qs : List (EAPoly k X.r)) :
    (addEqs X Qs).c = X.c := rfl

@[simp] theorem addEqs_fmt {k : ℕ} (X : SemiPf k) (Qs : List (EAPoly k X.r)) :
    (addEqs X Qs).fmt = X.fmt := rfl

/-- The point set of `addEqs X Qs`: the points of `X` at which every `Q ∈ Qs` vanishes. -/
theorem addEqs_set {k : ℕ} (X : SemiPf k) (Qs : List (EAPoly k X.r)) :
    (addEqs X Qs).set = X.set ∩ {z | ∀ Q ∈ Qs, eaEval X.c Q z = 0} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, SemiPf.set, addEqs]
  constructor
  · rintro ⟨hc, B, hB, hholds⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    exact ⟨⟨hc, B₀, hB₀, ⟨fun f hf => hholds.1 f (List.mem_append.mpr (Or.inl hf)),
        hholds.2⟩⟩, fun Q hQ => hholds.1 Q (List.mem_append.mpr (Or.inr hQ))⟩
  · rintro ⟨⟨hc, B₀, hB₀, hholds⟩, hQ⟩
    refine ⟨hc, ⟨B₀.eqs ++ Qs, B₀.pos⟩, List.mem_map.mpr ⟨B₀, hB₀, rfl⟩, ?_, hholds.2⟩
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hholds.1 f hf
    · exact hQ f hf

/-! ## The padded semi-Pfaffian set -/

/-- View `X ⊆ ℝ^{p+q}` as a semi-Pfaffian set in `ℝ^{p+(d+q)}` by inserting `d` coordinates
between the base and the fibre coordinates, all pinned to `0`. -/
@[reducible] def padStrat (p q d : ℕ) (X : SemiPf (p + q)) : SemiPf (p + (d + q)) where
  r := X.r
  c := Work.WilE8.EAChain.extend (midInj p d q) X.c
  basics := X.basics.map (fun B =>
    (⟨B.eqs.map (Work.WilE8.EAPoly.extend (midInj p d q)) ++ pins p d q X.r,
      B.pos.map (Work.WilE8.EAPoly.extend (midInj p d q))⟩ : Basic (p + (d + q)) X.r))

@[simp] theorem padStrat_r (p q d : ℕ) (X : SemiPf (p + q)) :
    (padStrat p q d X).r = X.r := rfl

@[simp] theorem padStrat_c (p q d : ℕ) (X : SemiPf (p + q)) :
    (padStrat p q d X).c = Work.WilE8.EAChain.extend (midInj p d q) X.c := rfl

@[simp] theorem padStrat_basics (p q d : ℕ) (X : SemiPf (p + q)) :
    (padStrat p q d X).basics =
      X.basics.map (fun B =>
        (⟨B.eqs.map (Work.WilE8.EAPoly.extend (midInj p d q)) ++ pins p d q X.r,
          B.pos.map (Work.WilE8.EAPoly.extend (midInj p d q))⟩ : Basic (p + (d + q)) X.r)) :=
  rfl

@[simp] theorem padStrat_fmt (p q d : ℕ) (X : SemiPf (p + q)) :
    (padStrat p q d X).fmt = p + (d + q) + X.r := rfl

/-- Evaluating an extended `EA`-polynomial against the extended chain is evaluating the
original polynomial at the substituted point. -/
theorem eaEval_extend_midInj {p q d r : ℕ} (c : EAChain (p + q) r) (Q : EAPoly (p + q) r)
    (z : Fin (p + (d + q)) → ℝ) :
    eaEval (Work.WilE8.EAChain.extend (midInj p d q) c)
        (Work.WilE8.EAPoly.extend (midInj p d q) Q) z
      = eaEval c Q (fun i => z (midInj p d q i)) :=
  Work.WilE8.Extend.extend_eaEval_inj (midInj_injective p d q) c Q z

/-- The basic sets of `padStrat` hold at `z` exactly when the original basic set holds at
`z ∘ midInj` and all the pinning equations vanish. -/
theorem padStrat_basic_holds {p q d : ℕ} (X : SemiPf (p + q)) (B : Basic (p + q) X.r)
    (z : Fin (p + (d + q)) → ℝ) :
    (⟨B.eqs.map (Work.WilE8.EAPoly.extend (midInj p d q)) ++ pins p d q X.r,
        B.pos.map (Work.WilE8.EAPoly.extend (midInj p d q))⟩ : Basic (p + (d + q)) X.r).holds
        (Work.WilE8.EAChain.extend (midInj p d q) X.c) z
      ↔ B.holds X.c (fun i => z (midInj p d q i)) ∧
        ∀ Q ∈ pins p d q X.r,
          eaEval (Work.WilE8.EAChain.extend (midInj p d q) X.c) Q z = 0 := by
  have hrew : ∀ f : EAPoly (p + q) X.r,
      eaEval (Work.WilE8.EAChain.extend (midInj p d q) X.c)
        (Work.WilE8.EAPoly.extend (midInj p d q) f) z
        = eaEval X.c f (fun i => z (midInj p d q i)) :=
    fun f => eaEval_extend_midInj X.c f z
  simp only [Basic.holds, List.forall_mem_append, List.forall_mem_map]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨fun f hf => by rw [← hrew f]; exact h1 f hf,
      fun g hg => by rw [← hrew g]; exact h3 g hg⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨⟨fun f hf => by rw [hrew f]; exact h1 f hf, h2⟩,
      fun g hg => by rw [hrew g]; exact h3 g hg⟩

/-- The point set of `padStrat`: the points whose coordinates outside the inserted block
satisfy `X`, with the inserted block pinned to `0`. -/
theorem padStrat_set {p q d : ℕ} (X : SemiPf (p + q)) :
    (padStrat p q d X).set =
      {z : Fin (p + (d + q)) → ℝ |
        (fun i => z (midInj p d q i)) ∈ X.set ∧ ∀ a : Fin d, z (midIdx p d q a) = 0} := by
  ext z
  simp only [SemiPf.set, padStrat, Set.mem_setOf_eq, padStrat_c]
  constructor
  · rintro ⟨hc, B, hB, hholds⟩
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.mp hB
    obtain ⟨hX, hpins⟩ := (padStrat_basic_holds X B₀ z).mp hholds
    refine ⟨⟨fun i => hc (midInj p d q i), B₀, hB₀, hX⟩, fun a => ?_⟩
    have := hpins (pinAt p d q X.r a) (pinAt_mem p d q X.r a)
    rwa [eaEval_pinAt] at this
  · rintro ⟨⟨hcube, B₀, hB₀, hX⟩, hz⟩
    have hcube' : z ∈ cubeC (p + (d + q)) := by
      intro j
      by_cases h1 : (j : ℕ) < p
      · have hj : j = midInj p d q (Fin.castAdd q (⟨(j : ℕ), h1⟩ : Fin p)) := by
          rw [midInj_castAdd]; exact Fin.ext rfl
        rw [hj]
        exact hcube _
      · by_cases h2 : (j : ℕ) < p + d
        · have hj : j = midIdx p d q (⟨(j : ℕ) - p, by omega⟩ : Fin d) := by
            refine Fin.ext ?_
            show (j : ℕ) = p + ((j : ℕ) - p)
            omega
          rw [hj, hz]
          norm_num
        · have hj : j = midInj p d q (Fin.natAdd p (⟨(j : ℕ) - p - d, by omega⟩ : Fin q)) := by
            rw [midInj_natAdd]
            refine Fin.ext ?_
            show (j : ℕ) = p + (d + ((j : ℕ) - p - d))
            omega
          rw [hj]
          exact hcube _
    refine ⟨hcube', _, List.mem_map.mpr ⟨B₀, hB₀, rfl⟩, ?_⟩
    refine (padStrat_basic_holds X B₀ z).mpr ⟨hX, fun Q hQ => ?_⟩
    obtain ⟨a, rfl⟩ := mem_pins.mp hQ
    rw [eaEval_pinAt]
    exact hz a

/-! ## Removing repeated basic sets -/

/-- Remove repeated basic sets.  The point set is unchanged, while the number of basic sets
becomes controlled by the degree. -/
@[reducible] def tidy {k : ℕ} (X : SemiPf k) : SemiPf k where
  r := X.r
  c := X.c
  basics := X.basics.dedup

@[simp] theorem tidy_r {k : ℕ} (X : SemiPf k) : (tidy X).r = X.r := rfl

@[simp] theorem tidy_c {k : ℕ} (X : SemiPf k) : (tidy X).c = X.c := rfl

@[simp] theorem tidy_fmt {k : ℕ} (X : SemiPf k) : (tidy X).fmt = X.fmt := rfl

@[simp] theorem tidy_basics {k : ℕ} (X : SemiPf k) : (tidy X).basics = X.basics.dedup := rfl

theorem tidy_set {k : ℕ} (X : SemiPf k) : (tidy X).set = X.set := by
  have h : ∀ z : Fin k → ℝ,
      (∃ B ∈ X.basics.dedup, B.holds X.c z) ↔ ∃ B ∈ X.basics, B.holds X.c z := by
    intro z
    constructor
    · rintro ⟨B, hB, hh⟩
      exact ⟨B, List.mem_dedup.mp hB, hh⟩
    · rintro ⟨B, hB, hh⟩
      exact ⟨B, List.mem_dedup.mpr hB, hh⟩
  ext z
  simp only [SemiPf.set, tidy, Set.mem_ofPred_eq]
  exact and_congr_right fun _ => h z

/-! ## The padded stratum -/

/-- The `d+q` defining functions of the padded stratum: first the `d` inserted coordinates, then
the pulled-back defining functions of `h`. -/
@[reducible] def padHead {p q d : ℕ} (r : ℕ) (h : Fin q → EAPoly (p + q) r) :
    Fin (d + q) → EAPoly (p + (d + q)) r :=
  fun a => if hh : (a : ℕ) < d then pinAt p d q r ⟨(a : ℕ), hh⟩
    else Work.WilE8.EAPoly.extend (midInj p d q) (h ⟨(a : ℕ) - d, by omega⟩)

theorem padHead_castAdd {p q d r : ℕ} (h : Fin q → EAPoly (p + q) r) (a : Fin d) :
    padHead r h (Fin.castAdd q a) = pinAt p d q r a := by
  have hlt : ((Fin.castAdd q a : Fin (d + q)) : ℕ) < d := by rw [Fin.val_castAdd]; exact a.isLt
  rw [padHead, dite_eq_left hlt]
  congr 1

theorem padHead_natAdd {p q d r : ℕ} (h : Fin q → EAPoly (p + q) r) (b : Fin q) :
    padHead r h (Fin.natAdd d b) = Work.WilE8.EAPoly.extend (midInj p d q) (h b) := by
  have hge : ¬ ((Fin.natAdd d b : Fin (d + q)) : ℕ) < d := by rw [Fin.val_natAdd]; omega
  rw [padHead, dite_eq_right hge]
  congr 1
  congr 1
  refine Fin.ext ?_
  show ((Fin.natAdd d b : Fin (d + q)) : ℕ) - d = (b : ℕ)
  rw [Fin.val_natAdd]
  omega

/-- The defining functions of `S`, viewed with the chain space of `tidy S.X`. -/
@[reducible] def tidyH {p q : ℕ} (S : Stratum p q) : Fin S.j → EAPoly (p + q) (tidy S.X).r :=
  fun a => S.h a

/-- The stratum obtained from `S : Stratum p q` by inserting `d` coordinates pinned to `0`
between the base and the fibre coordinates. -/
@[reducible] def padStratS (p q d : ℕ) (S : Stratum p q) (hj : S.j = q) : Stratum p (d + q) where
  X := padStrat p q d (tidy S.X)
  j := d + q
  h := padHead (tidy S.X).r (fun b => tidyH S (Fin.cast hj.symm b))

theorem padStratS_X {p q d : ℕ} (S : Stratum p q) (hj : S.j = q) :
    (padStratS p q d S hj).X = padStrat p q d (tidy S.X) := rfl

theorem padStratS_j {p q d : ℕ} (S : Stratum p q) (hj : S.j = q) :
    (padStratS p q d S hj).j = d + q := rfl

theorem padStratS_h {p q d : ℕ} (S : Stratum p q) (hj : S.j = q) :
    (padStratS p q d S hj).h = padHead (tidy S.X).r (fun b => tidyH S (Fin.cast hj.symm b)) :=
  rfl

theorem padStratS_h_castAdd {p q d : ℕ} (S : Stratum p q) (hj : S.j = q) (a : Fin d) :
    (padStratS p q d S hj).h (Fin.castAdd q a) = pinAt p d q (tidy S.X).r a := by
  rw [padStratS_h, padHead_castAdd]

theorem padStratS_h_natAdd {p q d : ℕ} (S : Stratum p q) (hj : S.j = q) (b : Fin q) :
    (padStratS p q d S hj).h (Fin.natAdd d b) =
      Work.WilE8.EAPoly.extend (midInj p d q) (S.h (Fin.cast hj.symm b)) := by
  rw [padStratS_h, padHead_natAdd]

/-! ## The sections of the padded stratum -/

/-- The section of the padded stratum corresponding to a section `s` of the fibre: append the `d`
zero coordinates. -/
def padSection (q d : ℕ) (s : Fin q → ℝ) : Fin (d + q) → ℝ :=
  Fin.addCases (fun _ : Fin d => (0 : ℝ)) s

theorem padSection_castAdd (q d : ℕ) (s : Fin q → ℝ) (a : Fin d) :
    padSection q d s (Fin.castAdd q a) = 0 :=
  Fin.addCases_left a

theorem padSection_natAdd (q d : ℕ) (s : Fin q → ℝ) (b : Fin q) :
    padSection q d s (Fin.natAdd d b) = s b :=
  Fin.addCases_right b

theorem projFirst_padSection (q d : ℕ) (s : Fin q → ℝ) :
    projFirst d q (padSection q d s) = 0 := by
  funext a
  exact padSection_castAdd q d s a

theorem projSnd_padSection (q d : ℕ) (s : Fin q → ℝ) :
    projSnd d q (padSection q d s) = s := by
  funext b
  exact padSection_natAdd q d s b

/-! ## The set of `padStrat` in terms of the inserted coordinates -/

/-- The injected coordinates of a point are the first `p` and last `q` coordinates, i.e. the
`Fin.append` of the base and the fibre part. -/
theorem midInj_append (p d q : ℕ) (z : Fin (p + (d + q)) → ℝ) (i : Fin (p + q)) :
    z (midInj p d q i) =
      Fin.append (projFirst p (d + q) z)
        (projSnd d q (projSnd p (d + q) z)) i := by
  by_cases h : (i : ℕ) < p
  · have hi : i = Fin.castAdd q (⟨(i : ℕ), h⟩ : Fin p) := Fin.ext rfl
    rw [hi, Fin.append_left]
    show z (midInj p d q (Fin.castAdd q (⟨(i : ℕ), h⟩ : Fin p)))
      = z (Fin.castAdd (d + q) (⟨(i : ℕ), h⟩ : Fin p))
    rw [midInj_castAdd]
  · have hi : i = Fin.natAdd p (⟨(i : ℕ) - p, by omega⟩ : Fin q) := by
      refine Fin.ext ?_
      show (i : ℕ) = p + ((i : ℕ) - p)
      omega
    rw [hi, Fin.append_right]
    show z (midInj p d q (Fin.natAdd p (⟨(i : ℕ) - p, by omega⟩ : Fin q)))
      = z (Fin.natAdd p (Fin.natAdd d (⟨(i : ℕ) - p, by omega⟩ : Fin q)))
    rw [midInj_natAdd]

/-- Function form of `midInj_append`. -/
theorem midInj_append_fun (p d q : ℕ) (z : Fin (p + (d + q)) → ℝ) :
    (fun i : Fin (p + q) => z (midInj p d q i)) =
      Fin.append (projFirst p (d + q) z) (projSnd d q (projSnd p (d + q) z)) := by
  funext i
  exact midInj_append p d q z i

/-- The inserted block of a point is exactly its `projFirst d q` in the fibre part. -/
theorem projFirst_projSnd_eq (p d q : ℕ) (z : Fin (p + (d + q)) → ℝ) (a : Fin d) :
    projFirst d q (projSnd p (d + q) z) a = z (midIdx p d q a) := rfl

theorem projFirst_midInj (p d q : ℕ) (z : Fin (p + (d + q)) → ℝ) :
    projFirst p q (fun i => z (midInj p d q i)) = projFirst p (d + q) z := by
  funext a
  show z (midInj p d q (Fin.castAdd q a)) = z (Fin.castAdd (d + q) a)
  rw [midInj_castAdd]

theorem projSnd_append_projFirst_projSnd (p d q : ℕ) (z : Fin (p + (d + q)) → ℝ) :
    projSnd p (d + q) z =
      Fin.append (projFirst d q (projSnd p (d + q) z))
        (projSnd d q (projSnd p (d + q) z)) := by
  conv_lhs => rw [← Fin.append_castAdd_natAdd (f := projSnd p (d + q) z)]
  rfl

theorem projFirst_append {p n : ℕ} (x : Fin p → ℝ) (v : Fin n → ℝ) :
    projFirst p n (Fin.append x v) = x := by
  funext i
  exact Fin.append_left x v i

theorem projSnd_append {p n : ℕ} (x : Fin p → ℝ) (v : Fin n → ℝ) :
    projSnd p n (Fin.append x v) = v := by
  funext j
  exact Fin.append_right x v j

theorem midIdx_append {p d q : ℕ} (x : Fin p → ℝ) (v : Fin (d + q) → ℝ) (a : Fin d) :
    projFirst d q v a = Fin.append x v (midIdx p d q a) := by
  rw [midIdx_eq_natAdd, Fin.append_right]
  rfl

/-- Membership in the padded set, for a point of the form `Fin.append x v`: the fibre part of
`v` must satisfy `X` and the inserted block of `v` must vanish. -/
theorem mem_padStrat_append {p q d : ℕ} (X : SemiPf (p + q)) (x : Fin p → ℝ)
    (v : Fin (d + q) → ℝ) :
    Fin.append x v ∈ (padStrat p q d X).set ↔
      Fin.append x (projSnd d q v) ∈ X.set ∧ projFirst d q v = 0 := by
  rw [padStrat_set]
  constructor
  · rintro ⟨hmem, hz⟩
    rw [midInj_append_fun, projFirst_append, projSnd_append] at hmem
    refine ⟨hmem, ?_⟩
    funext a
    rw [midIdx_append x v a]
    exact hz a
  · rintro ⟨hmem, hz⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [midInj_append_fun, projFirst_append, projSnd_append]
      exact hmem
    · have h := congrFun hz a
      rw [midIdx_append x v a] at h
      exact h

theorem projSnd_midInj_projSnd (p d q : ℕ) (z : Fin (p + (d + q)) → ℝ) :
    projSnd p q (fun i => z (midInj p d q i)) = projSnd d q (projSnd p (d + q) z) := by
  funext b
  show z (midInj p d q (Fin.natAdd p b)) = z (Fin.natAdd p (Fin.natAdd d b))
  rw [midInj_natAdd]

theorem padSection_eq_append (q d : ℕ) (s : Fin q → ℝ) :
    padSection q d s = Fin.append (fun _ : Fin d => (0 : ℝ)) s := rfl

theorem append_projFirst_projSnd (p n : ℕ) (z : Fin (p + n) → ℝ) :
    Fin.append (projFirst p n z) (projSnd p n z) = z :=
  Fin.append_castAdd_natAdd

theorem continuous_padSection (q d : ℕ) :
    Continuous (fun v : Fin q → ℝ => padSection q d v) := by
  rw [continuous_pi_iff]
  intro i
  by_cases h : (i : ℕ) < d
  · have hi : i = Fin.castAdd q (⟨(i : ℕ), h⟩ : Fin d) := Fin.ext rfl
    rw [hi]
    have : (fun a : Fin q → ℝ => padSection q d a (Fin.castAdd q (⟨(i : ℕ), h⟩ : Fin d)))
        = fun _ => (0 : ℝ) := by
      funext a
      exact padSection_castAdd q d a _
    rw [this]
    exact continuous_const
  · have hi : i = Fin.natAdd d (⟨(i : ℕ) - d, by omega⟩ : Fin q) := by
      refine Fin.ext ?_
      show (i : ℕ) = d + ((i : ℕ) - d)
      omega
    rw [hi]
    have : (fun a : Fin q → ℝ =>
        padSection q d a (Fin.natAdd d (⟨(i : ℕ) - d, by omega⟩ : Fin q)))
        = fun a => a (⟨(i : ℕ) - d, by omega⟩ : Fin q) := by
      funext a
      exact padSection_natAdd q d a _
    rw [this]
    exact continuous_apply _

theorem continuousOn_padSection (p q d k : ℕ) (C : Set (Fin p → ℝ))
    (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)) (hcont : ∀ j, ContinuousOn (s j) C) (j : Fin k) :
    ContinuousOn (fun x => padSection q d (s j x)) C :=
  (continuous_padSection q d).comp_continuousOn (hcont j)

theorem padStratS_X_c {p q d : ℕ} (S : Stratum p q) (hj : S.j = q) :
    (padStratS p q d S hj).X.c = Work.WilE8.EAChain.extend (midInj p d q) S.X.c := rfl

/-- Evaluation of a pinned defining function of the padded stratum. -/
theorem eaEval_padStratS_h_castAdd {p q d : ℕ} (S : Stratum p q) (hj : S.j = q)
    (z : Fin (p + (d + q)) → ℝ) (a : Fin d) :
    eaEval (padStratS p q d S hj).X.c ((padStratS p q d S hj).h (Fin.castAdd q a)) z
      = z (midIdx p d q a) := by
  rw [padStratS_h_castAdd]
  exact eaEval_pinAt _ a z

/-- Evaluation of a pulled-back defining function of the padded stratum. -/
theorem eaEval_padStratS_h_natAdd {p q d : ℕ} (S : Stratum p q) (hj : S.j = q)
    (z : Fin (p + (d + q)) → ℝ) (b : Fin q) :
    eaEval (padStratS p q d S hj).X.c ((padStratS p q d S hj).h (Fin.natAdd d b)) z
      = eaEval S.X.c (S.h (Fin.cast hj.symm b)) (fun i => z (midInj p d q i)) := by
  rw [padStratS_h_natAdd]
  exact eaEval_extend_midInj S.X.c (S.h (Fin.cast hj.symm b)) z

end Work.WilE7
