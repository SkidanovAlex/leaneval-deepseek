/-
  Area E7 (Binyamini–Vorobjov, "effective fiber cutting" / BV Lemma 8).

  Vocabulary needed to run BV's induction on the *fibre dimension* `q - S.j` of a `Good`
  stratum:

  * `critMinor S l σ` — the `(j+1)×(j+1)`-minor of the matrix `[∂_y h ; e_l]` with columns `σ`,
    packaged as an EA polynomial over the *same* chain as `S.X`;
  * `critSet S l` — the fibre-critical set of the fibre coordinate `l` on `S`:
    `S.X.set ∩ {z | all (j+1)-minors of [∂_y h(z) ; e_l] vanish}`, a `SemiPf (p+q)` set over the
    same chain.

  Both the frontier step (`fiberClosure S.X.set \ S.X.set`) and the critical step (`critSet S l`)
  of BV's reduction produce again `SemiPf` sets, which are then re-stratified with `E5_strat`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Bounds.totalDegree_detOp_le

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The `l`-th fibre coordinate of `Fin (p+q)`. -/
abbrev fibDir (p q : ℕ) (l : Fin q) : Fin (p + q) := Fin.natAdd p l

/-- The `(j+1)×(j+1)`-minor of `[∂_y h ; e_l]` with columns `σ`, as an EA polynomial over the
same chain: the rows are `h 0, …, h (j-1)` and the coordinate function `y_l`, the columns are the
fibre derivatives `∂_{σ 0}, …, ∂_{σ j}`. -/
def critMinor {p q r j : ℕ} (c : EAChain (p + q) r) (h : Fin j → EAPoly (p + q) r) (l : Fin q)
    (σ : Fin (j + 1) → Fin q) : EAPoly (p + q) r :=
  detOp c h (fun b : Fin j => fibDir p q (σ (Fin.castSucc b)))
    (fibDir p q (σ (Fin.last j))) (MvPolynomial.X (Sum.inl (fibDir p q l)))

/-- The list of all `(j+1)×(j+1)`-minors of `[∂_y h ; e_l]`. -/
def critMinors {p q : ℕ} (S : Stratum p q) (l : Fin q) : List (EAPoly (p + q) S.X.r) :=
  ((Finset.univ : Finset (Fin (S.j + 1) → Fin q)).toList).map
    (fun σ => critMinor S.X.c S.h l σ)

/-- The fibre-critical set of the fibre coordinate `l` on the stratum `S`: the points of `S.X.set`
at which every `(S.j+1)`-minor of the matrix `[∂_y h ; e_l]` vanishes, i.e. at which `y_l` is
critical on the fibre germ.  It is a semi-Pfaffian set over the same chain as `S.X`. -/
def critSet {p q : ℕ} (S : Stratum p q) (l : Fin q) : SemiPf (p + q) :=
  ⟨S.X.r, S.X.c,
   S.X.basics.map (fun B => { eqs := B.eqs ++ critMinors S l, pos := B.pos })⟩

@[simp] theorem critSet_r {p q : ℕ} (S : Stratum p q) (l : Fin q) : (critSet S l).r = S.X.r := rfl
@[simp] theorem critSet_c {p q : ℕ} (S : Stratum p q) (l : Fin q) : (critSet S l).c = S.X.c := rfl
@[simp] theorem critSet_basics {p q : ℕ} (S : Stratum p q) (l : Fin q) :
    (critSet S l).basics =
      S.X.basics.map (fun B => { eqs := B.eqs ++ critMinors S l, pos := B.pos }) := rfl

/-- `critSet` does not change the format. -/
theorem critSet_fmt {p q : ℕ} (S : Stratum p q) (l : Fin q) :
    (critSet S l).fmt = S.X.fmt := rfl

/-- The set of `critSet S l`: the points of `S.X.set` where all the critical minors vanish. -/
theorem critSet_set {p q : ℕ} (S : Stratum p q) (l : Fin q) :
    (critSet S l).set = S.X.set ∩ {z | ∀ σ : Fin (S.j + 1) → Fin q,
      eaEval S.X.c (critMinor S.X.c S.h l σ) z = 0} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, SemiPf.set, critSet_basics, critSet_c]
  constructor
  · rintro ⟨hc, B, hB, hBholds⟩
    obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hB
    refine ⟨⟨hc, B', hB',
      ⟨fun f hf => hBholds.1 f (List.mem_append.mpr (Or.inl hf)), fun g hg => hBholds.2 g hg⟩⟩,
      fun σ => hBholds.1 _ ?_⟩
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨σ, Finset.mem_toList.mpr (Finset.mem_univ σ), rfl⟩))
  · rintro ⟨⟨hc, B, hB, hBholds⟩, hcrit⟩
    refine ⟨hc, _, List.mem_map.mpr ⟨B, hB, rfl⟩, ?_⟩
    refine ⟨fun f hf => ?_, hBholds.2⟩
    rcases List.mem_append.mp hf with hf | hf
    · exact hBholds.1 f hf
    · obtain ⟨σ, _, rfl⟩ := List.mem_map.mp hf
      exact hcrit σ

/-- `critSet` is contained in the stratum. -/
theorem critSet_subset {p q : ℕ} (S : Stratum p q) (l : Fin q) :
    (critSet S l).set ⊆ S.X.set := by
  rw [critSet_set]; exact Set.inter_subset_left

end Work.WilE7
