import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.RatHurewicz.LensSpace.Basic
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.EMFG.lensSpaceEM
import Submission.Work.EMFG.sphereBallContractible
import Submission.Work.EMFG.lensSeparation
import Submission.Work.EMFG.lensIsometry
import Submission.Work.EMFG.lensBall_smul
import Submission.Work.EMFG.coveringInjOnHomeomorph
import Submission.Work.EMFG.contractibleSpace_pi
import Submission.Work.EMFG.piSubtypeHomeo
import Submission.Work.ThomBordism.finiteGoodCoverHomology
import Submission.Work.ThomBordism.homologyFinite_of_isRetract
import Submission.Work.EMFG.lensMultiplierUnique
import Submission.Work.EMFG.piGoodFamFG
import Submission.Work.EMFG.isEMSpaceUpTo_pi

set_option synthInstance.maxHeartbeats 400000

/-!
# EMFG — a small model of `K(A,1)` for a finite abelian `A`

`Work.EMFG.finiteAbelianModelFG`: for every *finite* abelian group `A` and every `N` there is a
space `X` with a base point `x` which is a model of `K(A,1)` through degree `N`
(`Work.Serre.IsEMSpaceUpTo A 1 _ N X x`) and whose integral homology is finitely generated through
degree `N - 1`.

## The model

`A` is a finite product of finite cyclic groups, `A ≃+ ∏ᵢ ZMod (nᵢ)` (`finiteAbelianEqProdZMod`,
from Mathlib's structure theorem).  The model is the product of the corresponding lens spaces

`X = ∏ᵢ S^{2N+3}/μ_{nᵢ}`.

* `Work.EMFG.isEMSpaceUpTo_lensSpace` (in `EMFG/lensSpaceEM.lean`) makes each factor a model of
  `K(ZMod nᵢ,1)` through degree `2N ⊇ N`, and `isEMSpaceUpTo_pi` promotes this to the product
  (`π_*` of a finite product is the product of the `π_*`);
* the finiteness of `H_*(X;ℤ)` comes from a finite *good cover* of each factor: the lens space is
  covered by the images of finitely many small balls of the sphere `S^{2N+3}`, and (for radius
  `ε < δ/8`, `δ` the uniform separation of the `μₙ`-orbit, `Work.EMFG.lensSeparation`) every
  nonempty finite intersection of these images is contractible.  The product of the good covers is a
  good cover of `X`, and `Work.EMFG.piGoodFamFG` (a finite good cover gives finitely generated
  homology) concludes.

The contractibility of the intersections is the substance: for a nonempty intersection one shows
that the "lift data" is unique up to a global translate (`lensMultiplierUnique`), so that the
intersection is the image of a single *piece* of the sphere — an intersection of balls of radius
`ε < 1`, which is contractible (`Work.EMFG.sphereBallContractible`) and is carried homeomorphically
onto its image by the covering map (`Work.EMFG.coveringInjOnHomeomorph`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.EMFG

noncomputable section

open scoped Topology
open CategoryTheory CategoryTheory.Limits

/-! ## The structure theorem for finite abelian groups -/

/-- **Structure theorem of finite abelian groups**, in the shape used below: every finite abelian
group is a finite product of finite cyclic groups. -/
theorem finiteAbelianEqProdZMod (A : Type) [AddCommGroup A] [Fintype A] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, n i ≠ 0) ∧ Nonempty (A ≃+ ((i : ι) → ZMod (n i))) := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' A
  letI := hι
  exact ⟨ι, hι, n, fun i => by have := hn i; omega,
    ⟨e.trans (DirectSum.addEquivProd fun i : ι => ZMod (n i))⟩⟩

/-- A base point of the lens sphere `S^{2N+3}`. -/
def lensBasePt (N : ℕ) : Work.RatHurewicz.lensTotal N :=
  ⟨EuclideanSpace.single 0 (1 : ℝ), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, EuclideanSpace.norm_single]
    norm_num⟩

/-! ## Range monotonicity of `IsEMSpaceUpTo` -/

/-- `IsEMSpaceUpTo` does not depend on the proof of `0 < m`. -/
theorem isEMSpaceUpTo_congr {A : Type} [AddCommGroup A] {m N : ℕ} {hm1 hm2 : 0 < m}
    {X : Type} [TopologicalSpace X] {x : X} (h : Work.Serre.IsEMSpaceUpTo A m hm1 N X x) :
    Work.Serre.IsEMSpaceUpTo A m hm2 N X x :=
  Eq.mp (congrArg (fun p => Work.Serre.IsEMSpaceUpTo A m p N X x)
    (Subsingleton.elim hm1 hm2)) h

/-- **Monotonicity in the range**: a model of `K(A,m)` through degree `N` is one through every
smaller degree. -/
theorem isEMSpaceUpTo_mono {A : Type} [AddCommGroup A] {m N N' : ℕ} {hm : 0 < m}
    {X : Type} [TopologicalSpace X] {x : X} (h : Work.Serre.IsEMSpaceUpTo A m hm N X x)
    (hNN' : N' ≤ N) : Work.Serre.IsEMSpaceUpTo A m hm N' X x :=
  ⟨h.1, fun i hi hc => h.2 i hi (hc.elim Or.inl fun hlt => Or.inr (le_trans hlt hNN'))⟩

/-- **The lens space is a model of `K(ZMod n,1)` through degree `N`.** -/
theorem lensSpaceEMUpTo (n N : ℕ) [NeZero n] (e₀ : Work.RatHurewicz.lensTotal N) :
    Work.Serre.IsEMSpaceUpTo (ZMod n) 1 (by norm_num) N (Work.RatHurewicz.lensSpace n N)
      (Work.RatHurewicz.lensProj n N e₀) :=
  isEMSpaceUpTo_mono (isEMSpaceUpTo_congr (isEMSpaceUpTo_lensSpace n N e₀)) (by omega)

/-- The quotient map to the lens space is invariant under the group action. -/
theorem lensProj_smul_fb {n N : ℕ} [NeZero n] (g : Multiplicative (ZMod n))
    (y : Work.RatHurewicz.lensTotal N) :
    Work.RatHurewicz.lensProj n N (g • y) = Work.RatHurewicz.lensProj n N y := by
  apply Quotient.sound
  change (MulAction.orbitRel (Multiplicative (ZMod n)) (Work.RatHurewicz.lensTotal N))
    (g • y) y
  rw [MulAction.orbitRel_apply]
  exact MulAction.mem_orbit y g

/-! ## TEMPORARY placeholders (to be replaced by the imports of the delegated modules) -/




/-! ## The good cover of the lens space -/

/-- The **piece** of the lens sphere cut out by the lift data `lam : β → μₙ`: the points `y` whose
`lam i`-translate lies in the ball of radius `ε` around `x i`, for every `i`. -/
def LPc {n N : ℕ} [NeZero n] {β : Type} (x : β → Work.RatHurewicz.lensTotal N) (ε : ℝ)
    (lam : β → Multiplicative (ZMod n)) : Set (Work.RatHurewicz.lensTotal N) :=
  {y | ∀ i, (lam i) • y ∈ Metric.ball (x i) ε}

theorem LPc_eq_iInter {n N : ℕ} [NeZero n] {β : Type}
    (x : β → Work.RatHurewicz.lensTotal N) (ε : ℝ) (lam : β → Multiplicative (ZMod n)) :
    LPc x ε lam = ⋂ i, Metric.ball ((lam i)⁻¹ • x i) ε := by
  ext y
  simp only [LPc, Set.mem_ofPred_eq, Set.mem_iInter, Metric.mem_ball]
  exact forall_congr' fun i => by
    rw [← lensIsometry n N ((lam i)⁻¹) ((lam i) • y) (x i), inv_smul_smul]

theorem LPc_isOpen {n N : ℕ} [NeZero n] {β : Type} [Fintype β]
    (x : β → Work.RatHurewicz.lensTotal N) (ε : ℝ) (lam : β → Multiplicative (ZMod n)) :
    IsOpen (LPc x ε lam) := by
  rw [show LPc x ε lam = ⋂ i, (fun y => (lam i) • y) ⁻¹' (Metric.ball (x i) ε) from by
    ext y; simp [LPc]]
  exact isOpen_iInter_of_finite fun i =>
    Metric.isOpen_ball.preimage (continuous_const_smul (lam i))

theorem LPc_contractible {n N : ℕ} [NeZero n] {β : Type} [Fintype β] (b : β)
    (x : β → Work.RatHurewicz.lensTotal N) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (lam : β → Multiplicative (ZMod n)) (hne : (LPc x ε lam).Nonempty) :
    ContractibleSpace ↥(LPc x ε lam) := by
  haveI : Nonempty β := ⟨b⟩
  have hset : LPc x ε lam
      = ⋂ i ∈ (Finset.univ : Finset β), Metric.ball ((lam i)⁻¹ • x i) ε := by
    rw [LPc_eq_iInter]
    ext y
    simp
  rw [hset] at hne ⊢
  exact sphereBallContractible Finset.univ Finset.univ_nonempty
    (fun i : β => (lam i)⁻¹ • x i) ε hε0 hε1 hne

/-- **The quotient map is injective on a small ball.** -/
theorem lensProj_injOn_ball {n N : ℕ} [NeZero n] {ε : ℝ}
    (hsep : ∀ (z : Work.RatHurewicz.lensTotal N) (g : Multiplicative (ZMod n)),
      g ≠ 1 → 2 * ε < dist (g • z) z) (z : Work.RatHurewicz.lensTotal N) :
    Set.InjOn (Work.RatHurewicz.lensProj n N) (Metric.ball z ε) := by
  intro a ha b hb hab
  have hmem : a ∈ MulAction.orbit (Multiplicative (ZMod n)) b := Quotient.exact hab
  obtain ⟨g, hg⟩ := hmem
  have hg' : g • b = a := hg
  by_cases hg1 : g = 1
  · rw [hg1] at hg'
    simpa using hg'.symm
  · exfalso
    have h1 := hsep b g hg1
    have h2 : dist (g • b) b < 2 * ε := by
      rw [hg']
      calc dist a b ≤ dist a z + dist z b := dist_triangle a z b
        _ < ε + ε := by
              rw [Metric.mem_ball] at ha hb
              linarith [dist_comm a z, dist_comm b z]
        _ = 2 * ε := by ring
    linarith

theorem lensProj_injOn_LPc {n N : ℕ} [NeZero n] {β : Type} (b : β) {ε : ℝ}
    (hsep : ∀ (z : Work.RatHurewicz.lensTotal N) (g : Multiplicative (ZMod n)),
      g ≠ 1 → 2 * ε < dist (g • z) z)
    (x : β → Work.RatHurewicz.lensTotal N) (lam : β → Multiplicative (ZMod n)) :
    Set.InjOn (Work.RatHurewicz.lensProj n N) (LPc x ε lam) := by
  refine Set.InjOn.mono ?_ (lensProj_injOn_ball hsep ((lam b)⁻¹ • x b))
  rw [LPc_eq_iInter]
  intro y hy
  exact Set.mem_iInter.mp hy b

/-- **A nonempty intersection of images of small balls on the lens space is contractible.** -/
theorem lens_proj_image_inter_contractible {n N : ℕ} [NeZero n] {β : Type} [Fintype β] (b : β)
    {m : ℕ} (x : Fin m → Work.RatHurewicz.lensTotal N) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsep : ∀ (z : Work.RatHurewicz.lensTotal N) (g : Multiplicative (ZMod n)),
      g ≠ 1 → 4 * ε < dist (g • z) z)
    (f : β → Fin m)
    (hne : (⋂ i : β, Work.RatHurewicz.lensProj n N '' Metric.ball (x (f i)) ε).Nonempty) :
    ContractibleSpace ↥(⋂ i : β, Work.RatHurewicz.lensProj n N '' Metric.ball (x (f i)) ε) := by
  classical
  haveI : Nonempty β := ⟨b⟩
  set U : β → Set (Work.RatHurewicz.lensSpace n N) :=
    fun i => Work.RatHurewicz.lensProj n N '' Metric.ball (x (f i)) ε
  have hZU : (⋂ i : β, Work.RatHurewicz.lensProj n N '' Metric.ball (x (f i)) ε)
      = ⋂ i, U i := rfl
  rw [hZU]
  obtain ⟨y, hy⟩ := hne
  have hyU : ∀ i, y ∈ U i := fun i => Set.mem_iInter.mp hy i
  obtain ⟨e, he⟩ := Work.RatHurewicz.lensProj_surjective n N y
  -- lift data for `e`
  have hlift : ∀ i : β, ∃ g : Multiplicative (ZMod n), g • e ∈ Metric.ball (x (f i)) ε := by
    intro i
    obtain ⟨z, hz, hzp⟩ := hyU i
    have h : Work.RatHurewicz.lensProj n N z = Work.RatHurewicz.lensProj n N e := by rw [hzp, he]
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hg' : g • e = z := hg
    exact ⟨g, by rw [hg']; exact hz⟩
  choose lam hlam using hlift
  have hpiece_ne : (LPc (fun i => x (f i)) ε lam).Nonempty := ⟨e, hlam⟩
  -- equality of the intersection with the image of the piece
  have hZeq : (⋂ i, U i)
      = Work.RatHurewicz.lensProj n N '' LPc (fun i => x (f i)) ε lam := by
    apply Set.Subset.antisymm
    · intro y' hy'
      have hy'U : ∀ i, y' ∈ U i := fun i => Set.mem_iInter.mp hy' i
      obtain ⟨z₀, hz₀, hz₀p⟩ := hy'U b
      have hlift' : ∀ i : β, ∃ g : Multiplicative (ZMod n),
          g • z₀ ∈ Metric.ball (x (f i)) ε := by
        intro i
        obtain ⟨z', hz', hz'p⟩ := hy'U i
        have h : Work.RatHurewicz.lensProj n N z' = Work.RatHurewicz.lensProj n N z₀ := by
          rw [hz'p, hz₀p]
        obtain ⟨g, hg⟩ := Quotient.exact h
        have hg' : g • z₀ = z' := hg
        exact ⟨g, by rw [hg']; exact hz'⟩
      choose mu hmu using hlift'
      obtain ⟨k, hk⟩ := lensMultiplierUnique b hsep (fun i => x (f i)) e z₀ lam mu hlam hmu
      exact ⟨k • z₀, fun i => by rw [← mul_smul, ← hk i]; exact hmu i,
        by rw [lensProj_smul_fb]; exact hz₀p⟩
    · rintro y' ⟨w, hw, rfl⟩
      refine Set.mem_iInter.mpr fun i => ⟨(lam i) • w, hw i, ?_⟩
      rw [lensProj_smul_fb]
  rw [hZeq]
  have hsep2 : ∀ (z : Work.RatHurewicz.lensTotal N) (g : Multiplicative (ZMod n)),
      g ≠ 1 → 2 * ε < dist (g • z) z := fun z g hg => by linarith [hsep z g hg]
  obtain ⟨φ, -⟩ := coveringInjOnHomeomorph (Work.RatHurewicz.lensProj n N)
    (Work.RatHurewicz.isCoveringMap_lensProj n N) (LPc_isOpen (fun i => x (f i)) ε lam)
    (lensProj_injOn_LPc b hsep2 (fun i => x (f i)) lam)
  haveI : ContractibleSpace ↥(LPc (fun i => x (f i)) ε lam) :=
    LPc_contractible b (fun i => x (f i)) hε0 hε1 lam hpiece_ne
  exact φ.contractibleSpace

/-! ## Finitely many balls cover the lens sphere -/

theorem exists_lens_ball_cover (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (x : Fin m → Work.RatHurewicz.lensTotal N),
      ∀ z : Work.RatHurewicz.lensTotal N, ∃ j, z ∈ Metric.ball (x j) ε := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun z : Work.RatHurewicz.lensTotal N => Metric.ball z ε) (fun z => Metric.isOpen_ball)
    (fun z _ => Set.mem_iUnion.mpr ⟨z, by rw [Metric.mem_ball, dist_self]; exact hε⟩)
  refine ⟨s.card, fun j => ((s.equivFin.symm j : {z // z ∈ s}) : Work.RatHurewicz.lensTotal N),
    fun z => ?_⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ z))
  obtain ⟨hjs, hjmem⟩ := Set.mem_iUnion.mp hj
  refine ⟨s.equivFin ⟨j, hjs⟩, ?_⟩
  show z ∈ Metric.ball (((s.equivFin.symm (s.equivFin ⟨j, hjs⟩) : {z // z ∈ s}) :
    Work.RatHurewicz.lensTotal N)) ε
  rw [show ((s.equivFin.symm (s.equivFin ⟨j, hjs⟩) : {z // z ∈ s}) :
    Work.RatHurewicz.lensTotal N) = j from by simp]
  exact hjmem

/-! ## The good family of the lens space -/

theorem lens_goodFam (n N : ℕ) [NeZero n] :
    ∃ (m : ℕ) (x : Fin m → Work.RatHurewicz.lensTotal N) (ε : ℝ), 0 < ε ∧
      (⋃ j, Work.RatHurewicz.lensProj n N '' Metric.ball (x j) ε) = Set.univ ∧
      Work.ThomBordism.IsGoodFam
        (fun j : Fin m => Work.RatHurewicz.lensProj n N '' Metric.ball (x j) ε) := by
  classical
  obtain ⟨δ, hδpos, hδsep⟩ := lensSeparation n
  set ε : ℝ := min (δ / 8) (1 / 2) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h4ε : 4 * ε < δ := by
    have h1 : ε ≤ δ / 8 := min_le_left _ _
    linarith
  have hsep : ∀ (z : Work.RatHurewicz.lensTotal N) (g : Multiplicative (ZMod n)),
      g ≠ 1 → 4 * ε < dist (g • z) z :=
    fun z g hg => lt_of_lt_of_le h4ε (hδsep N g hg z)
  obtain ⟨m, x, hcov⟩ := exists_lens_ball_cover N hε0
  refine ⟨m, x, ε, hε0, ?_, ?_⟩
  · rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨e, he⟩ := Work.RatHurewicz.lensProj_surjective n N y
    obtain ⟨j, hj⟩ := hcov e
    exact Set.mem_iUnion.mpr ⟨j, e, hj, he⟩
  · refine ⟨fun j => (Work.RatHurewicz.isCoveringMap_lensProj n N).isOpenMap _
      Metric.isOpen_ball, fun β _ f b hne => ?_⟩
    exact lens_proj_image_inter_contractible b x hε0 hε1 hsep f hne

/-! ## The theorem -/

theorem finiteAbelianModelFG (A : Type) [AddCommGroup A] [Fintype A] :
    ∀ N : ℕ, ∃ (X : Type) (_ : TopologicalSpace X) (x : X),
      Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N X x ∧ Work.PiS.FGUpTo X (N - 1) := by
  intro N
  obtain ⟨ι, hι, n, hn, ⟨eA⟩⟩ := finiteAbelianEqProdZMod A
  letI : Fintype ι := hι
  haveI hnz : ∀ i, NeZero (n i) := fun i => ⟨hn i⟩
  refine ⟨(i : ι) → Work.RatHurewicz.lensSpace (n i) N, inferInstance,
    fun i => Work.RatHurewicz.lensProj (n i) N (lensBasePt N), ?_, ?_⟩
  · have h1 : Work.Serre.IsEMSpaceUpTo ((i : ι) → ZMod (n i)) 1 (by norm_num) N
        ((i : ι) → Work.RatHurewicz.lensSpace (n i) N)
        (fun i => Work.RatHurewicz.lensProj (n i) N (lensBasePt N)) :=
      isEMSpaceUpTo_pi (by norm_num)
        (fun i => Work.RatHurewicz.lensProj (n i) N (lensBasePt N))
        (fun i => lensSpaceEMUpTo (n i) N (lensBasePt N))
    exact isEMSpaceUpTo_congr (Work.RatHurewicz.isEMSpaceUpTo_of_addEquiv
      (by norm_num) _ h1 eA.symm)
  · intro k hk
    have hL : ∀ i : ι, ∃ (m : ℕ) (x : Fin m → Work.RatHurewicz.lensTotal N) (ε : ℝ),
        0 < ε ∧
        (⋃ j, Work.RatHurewicz.lensProj (n i) N '' Metric.ball (x j) ε) = Set.univ ∧
        Work.ThomBordism.IsGoodFam
          (fun j : Fin m => Work.RatHurewicz.lensProj (n i) N '' Metric.ball (x j) ε) :=
      fun i => lens_goodFam (n i) N
    choose m x ε _ hcov hgood using hL
    exact piGoodFamFG (fun i (j : Fin (m i)) =>
      Work.RatHurewicz.lensProj (n i) N '' Metric.ball (x i j) (ε i)) hgood hcov k

end

end Work.EMFG
