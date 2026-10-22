import Mathlib
import Submission.Work.ATOM.ZS.NullSeqMaps
import Submission.Work.ATOM.ZS.PsiLiftDefs
import Submission.Work.ATOM.ZS.e_pred_eq_of_psi_infty
import Submission.Work.ATOM.ZS.psiN_gBig_finite
import Submission.Work.ATOM.ZS.psiN_gBig_infty

/-!
# AREA ATOM / `ℤ[S]`: the identity `zmap ψ ≫ g = ẑ - ẽ` (the finite-index part of `h₁`)

`gBig S : ℤ[ℕ∪{∞}] ⟶ ℤ[S]` is the null sequence of `NOTES_LEAD_solid_gaps1.md` §3.2, the descent
of `ĝ = [pr₂] - [β]` over `T' ⟶ ℕ∪{∞}`.  The identity of `REFS/03 §1` used in `h₁` is that
precomposing `g` with `ψ` produces the difference of the two idempotents `e_k` and `e_{k-1}`:

`zmap ψ ≫ g = zmap ê - zmap ẽ`   on `(ℕ∪{∞}) × S`,

where `ẽ(k,x) = e_{k-1}x` and `ê(k,x) = e_k x = shift ∘ ẽ` (`Work.ATOM.eShift`).

The proof is by exhibiting the *graph map*

`σ : (ℕ∪{∞}) × S ⟶ T'`,  `σ(k,x) = (ψ(k,x), e_k x)`

of `ψ`.  It is continuous for trivial reasons (it is a pair of continuous maps), and it satisfies
`σ ≫ tProj = ψ`, so `zmap ψ ≫ g = zmap σ ≫ (zmap tProj ≫ g) = zmap σ ≫ ĝ` by `gBig_spec`
(descent of `g`).  On `T'` everything is a `zmap`-combination, so it remains to check the two
pointwise identities `σ ≫ pr₂T = ê` and `σ ≫ β = ẽ`:

* on `ψ(k,x) = j ∈ ℕ` one has `e_k x = a_j` (and `n(j) = k`), so `pr₂T (σ(k,x)) = e_k x` and
  `β(j, a_j) = e_{n(j)-1}a_j = e_{k-1}(e_k x) = e_{k-1}x` (`e_comp`);
* on `ψ(k,x) = ∞` one has `e_{k-1}x = e_k x` (`Work.ATOM.ZS.e_pred_eq_of_psi_infty`; the case
  `k = ∞` is immediate), while `tProj (σ(k,x)) = ∞` forces `β = pr₂T` on `T'`.

The two pointwise inputs are proved in the sibling files `psiN_gBig_finite.lean` and
`psiN_gBig_infty.lean`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint

noncomputable section

namespace Work.ATOM.ZS

variable (S : LightProfinite.{0}) [Infinite S]

/-! ## The graph map `σ` of `ψ` -/

/-- The pair `(ψ(p), ê(p))` lies in `T' = {(j,a_j)} ∪ {∞}×S`. -/
theorem psiN_gBig_mem_tSet (p : ↥(Work.ATOM.NS S)) :
    Work.ATOM.mkNS S (Work.ATOM.psiN S p) (Work.ATOM.eShift S p) ∈ Work.ATOM.tSet S := by
  rw [Work.ATOM.mem_tSet_iff]
  by_cases h : Work.ATOM.psiN S p = ∞
  · exact Or.inl h
  · obtain ⟨j, hj⟩ := OnePoint.ne_infty_iff_exists.mp h
    have hj' : Work.ATOM.psiN S p = ((j : ℕ) : ℕ∪{∞}) := hj.symm
    obtain ⟨k, x, hp, ha, _⟩ := psiN_gBig_finite S p j hj'
    refine Or.inr ⟨j, hj', ?_⟩
    rw [hp, Work.ATOM.eShift_some, ha]

/-- **The graph map of `ψ`**: `σ(p) = (ψ(p), ê(p))`, a point of `T'`. -/
def psiN_gBig_sigma : Work.ATOM.NS S ⟶ Work.ATOM.T' S :=
  ConcreteCategory.ofHom
    ⟨fun p => (⟨Work.ATOM.mkNS S (Work.ATOM.psiN S p) (Work.ATOM.eShift S p),
        psiN_gBig_mem_tSet S p⟩ : ↥(Work.ATOM.T' S)),
      Continuous.subtype_mk
        (Continuous.prodMk (ConcreteCategory.hom (Work.ATOM.psiN S)).continuous_toFun
          (ConcreteCategory.hom (Work.ATOM.eShift S)).continuous_toFun)
        (fun p => psiN_gBig_mem_tSet S p)⟩

@[simp] lemma psiN_gBig_sigma_fst (p : ↥(Work.ATOM.NS S)) :
    (psiN_gBig_sigma S p).1 = Work.ATOM.mkNS S (Work.ATOM.psiN S p) (Work.ATOM.eShift S p) := rfl

/-- The first projection of `σ` is `ψ`. -/
@[simp] theorem psiN_gBig_sigma_tProj :
    psiN_gBig_sigma S ≫ Work.ATOM.tProj S = Work.ATOM.psiN S := by
  apply ConcreteCategory.hom_ext
  intro p
  rw [ConcreteCategory.comp_apply, Work.ATOM.tProj_apply, psiN_gBig_sigma_fst]

/-- The second projection of `σ` is `ê`. -/
@[simp] theorem psiN_gBig_sigma_pr₂T :
    psiN_gBig_sigma S ≫ Work.ATOM.pr₂T S = Work.ATOM.eShift S := by
  apply ConcreteCategory.hom_ext
  intro p
  rw [ConcreteCategory.comp_apply, Work.ATOM.pr₂T_apply, psiN_gBig_sigma_fst]

/-! ## The value of `ẽ` on `(k,x)` -/

/-- `ẽ(k,x) = s₀` for `k = 0` and `e_{k-1}x` otherwise, uniformly in `k`. -/
lemma psiN_gBig_ePredFun_mkNS (k : ℕ) (x : ↥S) :
    Work.ATOM.ePredFun S (Work.ATOM.mkNS S ((k : ℕ) : ℕ∪{∞}) x) =
      (if k = 0 then (Work.ATOM.levelData S).s₀ else Work.ATOM.e S (k - 1) x) := by
  simp only [Work.ATOM.ePredFun, OnePoint.elim_some]

/-- **The value of `β` on `σ(p)`**: `β(ψ(p), ê(p)) = ẽ(p)`, the finite-`ψ` case. -/
lemma psiN_gBig_betaFun_eq (k : ℕ) (x : ↥S) (j : ℕ)
    (ha : Work.ATOM.e S k x = (Work.ATOM.levelData S).a j)
    (hl : Work.ATOM.lvl S j = k) :
    Work.ATOM.betaFun S (((j : ℕ) : ℕ∪{∞}), Work.ATOM.e S k x) =
      Work.ATOM.ePredFun S (Work.ATOM.mkNS S ((k : ℕ) : ℕ∪{∞}) x) := by
  rw [ha, Work.ATOM.betaFun_lvl (S := S) j ((Work.ATOM.levelData S).a j), hl,
    psiN_gBig_ePredFun_mkNS]
  by_cases hk : k = 0
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]
    -- `e_{k-1} a_j = e_{k-1} (e_k x) = e_{min k (k-1)} x = e_{k-1} x`
    have hcomp : Work.ATOM.e S (k - 1) (Work.ATOM.e S k x) = Work.ATOM.e S (k - 1) x := by
      have h := ConcreteCategory.congr_hom ((Work.ATOM.levelData S).e_comp k (k - 1)) x
      rwa [CategoryTheory.comp_apply, Nat.min_eq_right (by omega : k - 1 ≤ k)] at h
    rw [← ha]
    exact hcomp

/-- **The second projection of `σ` composed with `β` is `ẽ`.** -/
theorem psiN_gBig_sigma_betaT :
    psiN_gBig_sigma S ≫ Work.ATOM.betaT S = Work.ATOM.ePred S := by
  apply ConcreteCategory.hom_ext
  intro p
  show Work.ATOM.betaFun S (Work.ATOM.mkNS S (Work.ATOM.psiN S p) (Work.ATOM.eShift S p)) =
    Work.ATOM.ePredFun S p
  by_cases h : Work.ATOM.psiN S p = ∞
  · rw [h, Work.ATOM.betaFun_infty, psiN_gBig_infty S p h]
    exact Work.ATOM.ePred_apply S p
  · obtain ⟨j, hj⟩ := OnePoint.ne_infty_iff_exists.mp h
    have hj' : Work.ATOM.psiN S p = ((j : ℕ) : ℕ∪{∞}) := hj.symm
    obtain ⟨k, x, hp, ha, hl⟩ := psiN_gBig_finite S p j hj'
    rw [hj', hp, Work.ATOM.eShift_some]
    exact psiN_gBig_betaFun_eq S k x j ha hl

/-! ## The identity -/

open CategoryTheory MonoidalCategory LightCondensed in
theorem psiN_gBig (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.zmap (Work.ATOM.psiN S) ≫ Work.ATOM.gBig S =
      Work.ATOM.zmap (Work.ATOM.eShift S) - Work.ATOM.zmap (Work.ATOM.ePred S) := by
  calc Work.ATOM.zmap (Work.ATOM.psiN S) ≫ Work.ATOM.gBig S
      = Work.ATOM.zmap (psiN_gBig_sigma S ≫ Work.ATOM.tProj S) ≫ Work.ATOM.gBig S := by
        rw [psiN_gBig_sigma_tProj]
    _ = (Work.ATOM.zmap (psiN_gBig_sigma S) ≫ Work.ATOM.zmap (Work.ATOM.tProj S)) ≫
          Work.ATOM.gBig S := by rw [zmap_comp]
    _ = Work.ATOM.zmap (psiN_gBig_sigma S) ≫
          (Work.ATOM.zmap (Work.ATOM.tProj S) ≫ Work.ATOM.gBig S) := by rw [Category.assoc]
    _ = Work.ATOM.zmap (psiN_gBig_sigma S) ≫ Work.ATOM.gHat S := by rw [Work.ATOM.gBig_spec]
    _ = Work.ATOM.zmap (psiN_gBig_sigma S) ≫
          (Work.ATOM.zmap (Work.ATOM.pr₂T S) - Work.ATOM.zmap (Work.ATOM.betaT S)) := by
        rw [Work.ATOM.gHat]
    _ = Work.ATOM.zmap (psiN_gBig_sigma S) ≫ Work.ATOM.zmap (Work.ATOM.pr₂T S) -
          Work.ATOM.zmap (psiN_gBig_sigma S) ≫ Work.ATOM.zmap (Work.ATOM.betaT S) := by
        rw [Preadditive.comp_sub]
    _ = Work.ATOM.zmap (psiN_gBig_sigma S ≫ Work.ATOM.pr₂T S) -
          Work.ATOM.zmap (psiN_gBig_sigma S ≫ Work.ATOM.betaT S) := by
        rw [zmap_comp, zmap_comp]
    _ = Work.ATOM.zmap (Work.ATOM.eShift S) - Work.ATOM.zmap (Work.ATOM.ePred S) := by
        rw [psiN_gBig_sigma_pr₂T, psiN_gBig_sigma_betaT]

end Work.ATOM.ZS
