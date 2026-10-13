/-
  WilE7 (`Submission.Work.WilE7.BelowAux.belowOpenDefs`): the semi-Pfaffian presentation of the
  **open** below cell of a sheet.

  The closed below cell of `Work.WilE7.BelowAux.BelowDefs` is presented by `belowS`, whose lower
  bound `-1 ≤ t` comes from the cube constraint on the vertical coordinate.  The cell needed by
  the assembly of the below band is the *open* one,

    `{y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s 0 (Fin.init y)) (Fin.last m)}`,

  with a **strict** lower bound, which is *not* the `belowExtract`-image of the connected component
  of `belowS` through the `-1`-point (that component does meet the hyperplane `t = -1`).

  This file cuts `belowS` by one further strict atom, `t + 1 > 0` (`belowOpenAtom`):

    `belowSopen Z S = belowS Z S ∩ {t > -1}`,

  and records its point set (`belowSopen_mem_iff`), the parametrised points (`belowPt_mem_open`),
  the parametrising region `belowHlt` (with the *strict* lower bound), the canonical interior
  vertical coordinate `belowT0` (the midpoint of `-1` and the level of sheet `0`), and the
  monotonicity of connected components along `belowSopen ⊆ belowS`.
-/
import Mathlib
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.BelowAux.belowComp_sub
import Submission.Work.WilE7.BelowAux.belowComp_cov
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.star_proj

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.BelowAux
open WilkiesDesign WilkiesDesign.E

/-! ## §1. The strict inequality atom `t > -1` -/

/-- The atom `t + 1`, positive exactly when the vertical coordinate is strictly above `-1`. -/
def belowOpenAtom (p m r : ℕ) : EAPoly (belowDim p m) r :=
  MvPolynomial.X (Sum.inl (belowTIdx p m)) + MvPolynomial.C (1 : ℝ)

theorem eaEval_belowOpenAtom {p m r : ℕ} (c : EAChain (belowDim p m) r)
    (w : Fin (belowDim p m) → ℝ) :
    eaEval c (belowOpenAtom p m r) w = belowT w + 1 := by
  simp [belowOpenAtom, eaEval, belowT]

/-! ## §2. The open below presentation -/

/-- The open below set: `belowS` cut by the strict inequality `t > -1`. -/
noncomputable def belowSopen {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    SemiPf (belowDim p m) :=
  Work.WilE7.SemiPf.addConds (belowS Z S) [] [belowOpenAtom p m (belowS Z S).r]

/-- **The point set of `belowSopen`**: the point set of `belowS`, with the strict additional
condition `-1 < t`. -/
theorem belowSopen_mem_iff {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (w : Fin (belowDim p m) → ℝ) :
    w ∈ (belowSopen Z S).set ↔ w ∈ (belowS Z S).set ∧ -1 < belowT w := by
  rw [belowSopen, Work.WilE7.SemiPf.addConds_set]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.not_mem_nil, IsEmpty.forall_iff,
    List.mem_cons, forall_eq_or_imp, forall_const, and_true, eaEval_belowOpenAtom]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩

theorem belowSopen_subset {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    (belowSopen Z S).set ⊆ (belowS Z S).set :=
  fun _ hw => ((belowSopen_mem_iff Z S _).mp hw).1

theorem belowSopen_fmt {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1)) :
    (belowSopen Z S).fmt = (belowS Z S).fmt :=
  Work.WilE7.SemiPf.addConds_fmt (belowS Z S) [] [belowOpenAtom p m (belowS Z S).r]

/-- Reindexing `belowSopen` along a permutation of the ambient coordinates does not change its
format (the ambient dimension is preserved: `(p+1) + belowFib p m = belowDim p m`). -/
theorem belowSopen_reindex_fmt {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (e : Fin (belowDim p m) ≃ Fin ((p + 1) + belowFib p m)) :
    (Work.WilE7.SemiPf.reindex e (belowSopen Z S)).fmt = (belowSopen Z S).fmt := by
  simp only [WilkiesDesign.E.SemiPf.fmt, Work.WilE7.SemiPf.reindex, belowFib, belowDim, belowK]
  omega

/-- A point of the connected component of `belowSopen` lies in the connected component of the
same point in `belowS` (the open set is contained in the closed one). -/
theorem component_belowSopen_subset {p m : ℕ} (Z : SemiPf (p + (m + 1)))
    (S : Stratum p (m + 1)) (q : Fin (belowDim p m) → ℝ) :
    connectedComponentIn (belowSopen Z S).set q ⊆ connectedComponentIn (belowS Z S).set q :=
  connectedComponentIn_mono q (belowSopen_subset Z S)

/-! ## §3. The parametrised points of `belowSopen` -/

/-- The parametrised point lies in `belowSopen` whenever its data satisfy the sheet condition,
the cube constraint and the *strict* inequalities `-1 < t < v₂`. -/
theorem belowPt_mem_open {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S : Stratum p (m + 1))
    (u : Fin (p + (m + 1)) → ℝ) (hu : u ∈ Z.set) (v : Fin (m + 1) → ℝ) (t : ℝ)
    (hv : Fin.append (projFirst p (m + 1) u) v ∈ S.X.set) (ht : |t| ≤ 1)
    (htlo : -1 < t) (h : t < v (Fin.last m)) :
    belowPt u v t ∈ (belowSopen Z S).set := by
  rw [belowSopen_mem_iff]
  exact ⟨belowPt_mem Z S u hu v t hv ht h, by rw [belowT_belowPt]; exact htlo⟩

/-! ## §4. The parametrising region with a strict lower bound -/

/-- The region of `(base component) × ℝ` parametrising the *open* below cell: the base point runs
over the component of `Z` through `u₀` and the vertical coordinate over `(-1, level of s j)`. -/
def belowHlt {p m k : ℕ} (Z : SemiPf (p + (m + 1)))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (u₀ : Fin (p + (m + 1)) → ℝ) : Set ((Fin (p + (m + 1)) → ℝ) × ℝ) :=
  {q | q.1 ∈ connectedComponentIn Z.set u₀ ∧ (-1 : ℝ) < q.2 ∧
    q.2 < (s j (projFirst p (m + 1) q.1)) (Fin.last m)}

theorem mem_belowHlt {p m k : ℕ} {Z : SemiPf (p + (m + 1))}
    {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {j : Fin k}
    {u₀ : Fin (p + (m + 1)) → ℝ} {q : (Fin (p + (m + 1)) → ℝ) × ℝ} :
    q ∈ belowHlt Z s j u₀ ↔ q.1 ∈ connectedComponentIn Z.set u₀ ∧ (-1 : ℝ) < q.2 ∧
      q.2 < (s j (projFirst p (m + 1) q.1)) (Fin.last m) := Iff.rfl

/-! ## §5. The canonical interior vertical coordinate -/

/-- The midpoint of `-1` and the level of the sheet `j` at the base of `u`.  It lies strictly
between `-1` and the level whenever the level exceeds `-1`. -/
def belowT0 {p m k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (u : Fin (p + (m + 1)) → ℝ) : ℝ :=
  (-1 + (s j (projFirst p (m + 1) u)) (Fin.last m)) / 2

theorem belowT0_gt {p m k : ℕ} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {j : Fin k}
    {u : Fin (p + (m + 1)) → ℝ}
    (h : -1 < (s j (projFirst p (m + 1) u)) (Fin.last m)) : -1 < belowT0 s j u := by
  rw [belowT0]; linarith

theorem belowT0_lt {p m k : ℕ} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {j : Fin k}
    {u : Fin (p + (m + 1)) → ℝ}
    (h : -1 < (s j (projFirst p (m + 1) u)) (Fin.last m)) :
    belowT0 s j u < (s j (projFirst p (m + 1) u)) (Fin.last m) := by
  rw [belowT0]; linarith

theorem belowT0_abs {p m k : ℕ} {s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)} {j : Fin k}
    {u : Fin (p + (m + 1)) → ℝ}
    (h1 : -1 < (s j (projFirst p (m + 1) u)) (Fin.last m))
    (h2 : (s j (projFirst p (m + 1) u)) (Fin.last m) ≤ 1) : |belowT0 s j u| ≤ 1 := by
  rw [belowT0, abs_le]
  constructor <;> linarith

end Work.WilE7.BelowAux
