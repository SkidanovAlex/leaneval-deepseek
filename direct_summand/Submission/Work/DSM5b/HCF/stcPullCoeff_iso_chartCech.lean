import Mathlib
import Submission.Work.DSM5b.HCF.PullCoeff
import Submission.Work.DSM5b.HCF.GSurjSign
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.Norm.ordIdxBijection

open CategoryTheory

set_option allowUnsafeReducibility true

set_option maxHeartbeats 4000000

attribute [local reducible] Work.DSM5b.HCF.pullCoeff Work.DSM5b.HCF.degZeroSubSys
  Work.DSM5b.HCF.locAtCoeff Work.DSM5b.CoeffSys.SubSys.toCoeff

namespace Work.DSM5b.HCF

universe u

variable {n : ℕ}

section Helpers

variable {m : ℕ}

/-- An increasing tuple is injective. -/
lemma incr_injective {ι : Type u} [LinearOrder ι] {m : ℕ} {τ : Fin (m + 1) → ι}
    (h : Work.DSM5b.IsIncr τ) : Function.Injective τ := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd hab (ne_of_lt (h a b hlt))
  · exact absurd hab.symm (ne_of_lt (h b a hgt))

/-- Pushing the values of a finset of `ULift (Fin n)` down to `Fin n` and back up is the identity. -/
lemma image_down_image_up (T : Finset (ULift.{u} (Fin n))) :
    (T.image ULift.down).image ULift.up = T := by
  rw [Finset.image_image]
  have h : (ULift.up ∘ ULift.down) = (id : ULift.{u} (Fin n) → ULift.{u} (Fin n)) :=
    funext fun x => ULift.up_down x
  rw [h, Finset.image_id]

/-- Pushing the values of a finset of `Fin n` up and back down is the identity. -/
lemma image_up_image_down (T : Finset (Fin n)) :
    (T.image (ULift.up : Fin n → ULift.{u} (Fin n))).image ULift.down = T := by
  rw [Finset.image_image]
  have h : ((ULift.down : ULift.{u} (Fin n) → Fin n) ∘ (ULift.up : Fin n → ULift.{u} (Fin n)))
      = (id : Fin n → Fin n) := funext fun x => rfl
  rw [h, Finset.image_id]

/-- The range of the increasing enumeration of a finset is the whole finset (as a subset of
`ULift (Fin n)`). -/
lemma tupRng_up_orderEmbOfFin (T : Finset (Fin n)) (h : T.card = m + 1) :
    Work.DSM5b.tupRng (fun i : Fin (m + 1) => ULift.up ((T.orderEmbOfFin h) i))
      = T.image (ULift.up : Fin n → ULift.{u} (Fin n)) := by
  ext y
  simp only [Work.DSM5b.tupRng, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(T.orderEmbOfFin h) i, Finset.orderEmbOfFin_mem T h i, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.range ⇑(T.orderEmbOfFin h) := by
      rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨i, hi⟩ := hx'
    exact ⟨i, by rw [hi]⟩

/-- **Increasing tuples of `ULift.{u} (Fin n)` correspond to `(m+1)`-element subsets of `Fin n`**,
by taking the range of the tuple and pushing it down along `ULift.down`. -/
noncomputable abbrev incrSubEquiv (m : ℕ) :
    IncrTuple (ι := ULift.{u} (Fin n)) m ≃ {S : Finset (Fin n) // S.card = m + 1} :=
  { toFun := fun τ => ⟨(Work.DSM5b.tupRng τ.1).image ULift.down, by
      rw [Finset.card_image_of_injective _ ULift.down_injective,
        Work.DSM5b.HCF.card_tupRng_of_isIncr τ]⟩
    invFun := fun S => ⟨fun i => ULift.up ((S.1.orderEmbOfFin S.2) i), fun i j hij =>
      (S.1.orderEmbOfFin S.2).strictMono hij⟩
    left_inv := fun τ => by
      apply Work.DSM5b.HCF.gIncrTup_ext
      show Work.DSM5b.tupRng (fun i : Fin (m + 1) =>
          ULift.up ((((Work.DSM5b.tupRng τ.1).image ULift.down).orderEmbOfFin
            (Finset.card_image_of_injective (Work.DSM5b.tupRng τ.1) ULift.down_injective ▸
              Work.DSM5b.HCF.card_tupRng_of_isIncr τ)) i)) = Work.DSM5b.tupRng τ.1
      rw [tupRng_up_orderEmbOfFin, image_down_image_up]
    right_inv := fun S => by
      apply Subtype.ext
      show ((Work.DSM5b.tupRng (fun i : Fin (m + 1) =>
        ULift.up ((S.1.orderEmbOfFin S.2) i))).image ULift.down) = S.1
      rw [tupRng_up_orderEmbOfFin, image_up_image_down] }

@[simp] lemma incrSubEquiv_apply_val (τ : IncrTuple (ι := ULift.{u} (Fin n)) m) :
    (incrSubEquiv (n := n) m τ).1 = (Work.DSM5b.tupRng τ.1).image ULift.down := rfl

@[simp] lemma incrSubEquiv_symm_apply_val (S : {S : Finset (Fin n) // S.card = m + 1})
    (i : Fin (m + 1)) :
    ((incrSubEquiv (n := n) m).symm S).1 i = ULift.up ((S.1.orderEmbOfFin S.2) i) := rfl

/-- The range of the inverse of `incrSubEquiv`. -/
lemma tupRng_incrSubEquiv_symm (S : {S : Finset (Fin n) // S.card = m + 1}) :
    Work.DSM5b.tupRng ((incrSubEquiv (n := n) m).symm S).1 = S.1.image ULift.up := by
  show Work.DSM5b.tupRng (fun i : Fin (m + 1) => ULift.up ((S.1.orderEmbOfFin S.2) i))
      = S.1.image ULift.up
  rw [tupRng_up_orderEmbOfFin]

end Helpers

section Crux

variable {m : ℕ}

/-- Deleting the `i`-th entry of an injective tuple of `ULift (Fin n)`, and pushing down, is the
same as erasing the deleted value. -/
lemma image_down_tupRng_tupDel (τ : Fin (m + 2) → ULift.{u} (Fin n))
    (hτ : Function.Injective τ) (i : Fin (m + 2)) :
    (Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ)).image ULift.down
      = ((Work.DSM5b.tupRng τ).image ULift.down).erase ((τ i).down) := by
  have h1 : Work.DSM5b.tupRng (Work.DSM5b.tupDel i τ) = (Work.DSM5b.tupRng τ).erase (τ i) :=
    Work.DSCOH.Norm.image_comp_succAbove_erase τ hτ i
  rw [h1, Finset.image_erase ULift.down_injective]

/-- For an increasing tuple, the position of an entry is the number of values below it. -/
lemma card_filter_image_down_lt (τ : Fin (m + 2) → ULift.{u} (Fin n))
    (hmono : StrictMono τ) (i : Fin (m + 2)) :
    (((Work.DSM5b.tupRng τ).image ULift.down).filter
      (fun j => j < (τ i).down)).card = (i : ℕ) := by
  rw [Work.DSM5b.tupRng, Finset.filter_image,
    Finset.card_image_of_injective _ ULift.down_injective]
  have hf : (Finset.univ.image τ).filter (fun k => k.down < (τ i).down)
      = (Finset.univ.image τ).filter (fun k => k < τ i) := by
    apply Finset.filter_congr
    intro k _
    exact ULift.down_lt
  rw [hf, Work.DSCOH.Norm.card_filter_lt_strictMono τ hmono i]

/-- The entries of an increasing tuple, pushed down, enumerate its value set. -/
noncomputable def finTupEquiv (τ : IncrTuple (ι := ULift.{u} (Fin n)) (m + 1)) :
    Fin (m + 2) ≃ ↥((Work.DSM5b.tupRng τ.1).image ULift.down) :=
  Equiv.ofBijective
    (fun i => ⟨(τ.1 i).down, by
      rw [Work.DSM5b.tupRng, Finset.mem_image]
      refine ⟨τ.1 i, ?_, rfl⟩
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨by
      rintro ⟨y, hy⟩
      rw [Finset.mem_image] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      rw [Work.DSM5b.tupRng, Finset.mem_image] at hz
      obtain ⟨i, -, hi⟩ := hz
      refine ⟨i, ?_⟩
      apply Subtype.ext
      show ULift.down (τ.1 i) = y
      rw [hi]; exact hzy, by
      rw [Fintype.card_fin, Fintype.card_coe,
        Finset.card_image_of_injective _ ULift.down_injective,
        Work.DSM5b.HCF.card_tupRng_of_isIncr τ]⟩)

@[simp] lemma finTupEquiv_apply (τ : IncrTuple (ι := ULift.{u} (Fin n)) (m + 1))
    (i : Fin (m + 2)) :
    (finTupEquiv (n := n) τ i).1 = (τ.1 i).down := rfl

end Crux

/-- `(-1 : ℤ) ^ k • x` and `(-1 : A) ^ k • x` agree. -/
lemma negOne_zsmul_eq_smul {A : Type*} [Ring A] {N : Type*} [AddCommGroup N] [Module A N]
    (k : ℕ) (x : N) : ((-1 : ℤ) ^ k) • x = ((-1 : A) ^ k) • x := by
  rw [← Int.cast_smul_eq_zsmul (R := A) ((-1 : ℤ) ^ k) x, Int.cast_pow, Int.cast_neg,
    Int.cast_one]

section Main

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
  [Module (Work.DSCOH.Poly R n) M] [IsScalarTower R (Work.DSCOH.Poly R n) M]
  (ℳ : ℕ → Submodule R M) [SetLike.GradedSMul (Work.DSCOH.homSub R n) ℳ]

/-- The termwise reindexing of the chart Čech complex into the sorted tuple complex: an
increasing tuple is sent to the range of its values, pushed down along `ULift.down`. -/
noncomputable def chartToStc (q : ℕ) :
    Work.DSCOH.CechTerm (A := R) (n := n) (M := M) ℳ q ≃ₗ[R]
      Work.DSM5b.Stc (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ) q :=
  LinearEquiv.piCongrLeft' (R := R)
    (φ := fun S : {S : Finset (Fin n) // S.card = q + 1} =>
      Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ S.1)
    ((incrSubEquiv (n := n) q).symm)

@[simp] lemma chartToStc_apply (q : ℕ) (y : Work.DSCOH.CechTerm (A := R) (n := n) (M := M) ℳ q)
    (τ : IncrTuple (ι := ULift.{u} (Fin n)) q) :
    chartToStc (n := n) (R := R) ℳ q y τ = y (incrSubEquiv (n := n) q τ) := rfl

/-- The value of `degPartRestrict` at an element. -/
lemma degPartRestrict_coe {S T : Finset (Fin n)}
    (ψ : Work.DSCOH.locAt (A := R) (n := n) (M := M) S →ₗ[Work.DSCOH.Poly R n]
      Work.DSCOH.locAt (A := R) (n := n) (M := M) T)
    (h : ∀ x ∈ Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ S,
      ψ x ∈ Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ T)
    (x : Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ S) :
    Work.DSCOH.degPartRestrict (A := R) (n := n) (M := M) ℳ ψ h x
      = ⟨ψ x.1, h x.1 x.2⟩ := rfl

/-- The value of the pullback coefficient system's restriction map. -/
lemma pullCoeff_res_eq {S T : Finset (ULift.{u} (Fin n))} (h : S ⊆ T)
    (x : (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ).M S) :
    (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ).res h x
      = ⟨Work.DSCOH.resAt (A := R) (n := n) (M := M)
            (Finset.image_subset_image (f := ULift.down) h) x.1,
          Work.DSCOH.resAt_degZero (A := R) (n := n) (M := M) (ℳ := ℳ)
            (Finset.image_subset_image (f := ULift.down) h) x.1 x.2⟩ := by
  apply Subtype.ext
  rfl

/-- The value of the pullback coefficient system's restriction map (as an element of `locAt`). -/
@[simp] lemma pullCoeff_res_val {S T : Finset (ULift.{u} (Fin n))} (h : S ⊆ T)
    (x : (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ).M S) :
    ((Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ).res h x).1
      = Work.DSCOH.resAt (A := R) (n := n) (M := M)
          (Finset.image_subset_image (f := ULift.down) h) x.1 := by
  rw [pullCoeff_res_eq]

/-- The value of `degPartRestrict` at an element (as an element of `locAt`). -/
@[simp] lemma degPartRestrict_val {S T : Finset (Fin n)}
    (ψ : Work.DSCOH.locAt (A := R) (n := n) (M := M) S →ₗ[Work.DSCOH.Poly R n]
      Work.DSCOH.locAt (A := R) (n := n) (M := M) T)
    (h : ∀ x ∈ Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ S,
      ψ x ∈ Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ T)
    (x : Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ S) :
    (Work.DSCOH.degPartRestrict (A := R) (n := n) (M := M) ℳ ψ h x).1 = ψ x.1 := by
  rw [degPartRestrict_coe]

/-- The restriction map is insensitive to the description of the subsets. -/
lemma resAt_val_eq {q : ℕ} {T : Finset (Fin n)}
    {S₁ S₂ : {S : Finset (Fin n) // S.card = q + 1}} (hS : S₁ = S₂)
    (h₁ : S₁.1 ⊆ T) (h₂ : S₂.1 ⊆ T)
    (y : (S : {S : Finset (Fin n) // S.card = q + 1}) →
      Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ S.1) :
    Work.DSCOH.resAt (A := R) (n := n) (M := M) h₁ (y S₁).1
      = Work.DSCOH.resAt (A := R) (n := n) (M := M) h₂ (y S₂).1 := by
  subst hS
  rfl

/-- The restriction of degree-zero parts is insensitive to the description of the subsets. -/
lemma degZero_resAt_congr {q : ℕ} {T : Finset (Fin n)}
    {S₁ S₂ : {S : Finset (Fin n) // S.card = q + 1}} (hS : S₁ = S₂)
    (h₁ : S₁.1 ⊆ T) (h₂ : S₂.1 ⊆ T)
    (y : (S : {S : Finset (Fin n) // S.card = q + 1}) →
      Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ S.1) :
    (⟨Work.DSCOH.resAt (A := R) (n := n) (M := M) h₁ (y S₁).1,
        Work.DSCOH.resAt_degZero (A := R) (n := n) (M := M) (ℳ := ℳ) h₁ (y S₁).1
          (y S₁).2⟩
      : Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ T)
      = ⟨Work.DSCOH.resAt (A := R) (n := n) (M := M) h₂ (y S₂).1,
        Work.DSCOH.resAt_degZero (A := R) (n := n) (M := M) (ℳ := ℳ) h₂ (y S₂).1
          (y S₂).2⟩ := by
  subst hS
  congr 1

end Main

/-- **The sorted tuple complex of the pullback coefficient system is the chart Čech complex.**
Let `R` be a commutative ring, `M` an `R[X_0,…,X_{n-1}]`-module (with `IsScalarTower R _ M`) and
`ℳ : ℕ → Submodule R M` a graded structure.  The "pullback" coefficient system
`Work.DSM5b.HCF.pullCoeff ℳ` on `ULift.{u} (Fin n)` has value `S ↦ degZero ℳ (S.image down)` at a
finite subset `S`.  Claim: the sorted tuple complex `stcComplex (pullCoeff ℳ)` (cochains on the
*increasing tuples* of `ULift.{u} (Fin n)`, with the `tupDel` differential) is isomorphic to the
chart Čech complex `Work.DSCOH.chartCech ℳ` (cochains indexed by the `(q+1)`-element subsets of
`Fin n`, with the alternating differential indexed by the elements of the subset).

Route: the increasing tuples `τ : Fin (q+1) → ULift (Fin n)` correspond bijectively to the
`(q+1)`-element subsets of `Fin n` by `τ ↦ (tupRng τ).image down` (use `IncrTuple`, injectivity of
an increasing tuple, and `Finset.orderIsoOfFin` for the inverse); since the coefficient systems are
literally the same under this correspondence (`pullCoeff ℳ`'s value at `S` is `degZero ℳ`
at `S.image down`), the termwise linear equivalence is `LinearEquiv.piCongr`-based, with the
identity on the coefficients.  For the commutation with the differentials one needs
`(tupRng (tupDel i τ)).image down = ((tupRng τ).image down).erase ((τ i).down)` and the sign
identity `(-1 : R) ^ i = (-1 : R) ^ ((filtermem).card)` for the finset `(tupRng τ).image down`,
i.e. the position `i` of `τ i` in an increasing tuple is the number of entries strictly below it,
which matches the sign `(-1)^{#{j ∈ T : j < i}}` of `Work.DSCOH.cechDiffComp`. -/
theorem stcPullCoeff_iso_chartCech {n : ℕ} {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (Work.DSCOH.Poly R n) M]
    [IsScalarTower R (Work.DSCOH.Poly R n) M] (ℳ : ℕ → Submodule R M)
    [SetLike.GradedSMul (Work.DSCOH.homSub R n) ℳ] :
    Nonempty ((Work.DSM5b.stcComplex (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ)) ≅
      (Work.DSCOH.chartCech (A := R) (n := n) (M := M) ℳ)) := by
  classical
  have chartCech_d (q : ℕ) :
      (Work.DSCOH.chartCech (A := R) (n := n) (M := M) ℳ).d q (q + 1) =
        ModuleCat.ofHom (Work.DSCOH.cechDiff (A := R) (n := n) (M := M) ℳ q) := by
    simp only [Work.DSCOH.chartCech, Work.DSCOH.chartCechOf, CochainComplex.of_d]
  have hcomm : ∀ (q : ℕ) (y : Work.DSCOH.CechTerm (A := R) (n := n) (M := M) ℳ q),
      Work.DSM5b.stcD (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ) q
          (chartToStc (n := n) (R := R) ℳ q y)
        = chartToStc (n := n) (R := R) ℳ (q + 1)
            (Work.DSCOH.cechDiff (A := R) (n := n) (M := M) ℳ q y) := by
    intro q y
    funext τ
    rw [Work.DSM5b.stcD_apply]
    change (∑ i : Fin (q + 2), (-1 : R) ^ (i : ℕ) •
          (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ).res
            (Work.DSM5b.tupRng_del_subset i τ.1)
            (y (incrSubEquiv (n := n) q ⟨Work.DSM5b.tupDel i τ.1, τ.2.tupDel i⟩)))
        = (Work.DSCOH.cechDiff (A := R) (n := n) (M := M) ℳ q y)
            (incrSubEquiv (n := n) (q + 1) τ)
    set T' : {S : Finset (Fin n) // S.card = q + 1 + 1} :=
      incrSubEquiv (n := n) (q + 1) τ with hT'_def
    have hT'_val : T'.1 = (Work.DSM5b.tupRng τ.1).image ULift.down := rfl
    have hT'_card : T'.1.card = q + 1 + 1 := T'.2
    have hmem : ∀ i' : Fin (q + 2), (τ.1 i').down ∈ T'.1 := by
      intro i'
      rw [hT'_val, Work.DSM5b.tupRng, Finset.mem_image]
      exact ⟨τ.1 i', by rw [Finset.mem_image]; exact ⟨i', Finset.mem_univ i', rfl⟩, rfl⟩
    let G : ↥T'.1 → Work.DSCOH.degZero (A := R) (n := n) (M := M) ℳ T'.1 := fun i =>
      (-1 : ℤ) ^ ((T'.1.filter fun j => j < i.1)).card •
        (Work.DSCOH.degPartRestrict (A := R) (n := n) (M := M) ℳ
          (Work.DSCOH.resAt (A := R) (n := n) (M := M) (Finset.erase_subset i.1 T'.1))
          (fun x hx => Work.DSCOH.resAt_degZero (A := R) (n := n) (M := M) (ℳ := ℳ)
            (Finset.erase_subset i.1 T'.1) x hx))
        (y ⟨T'.1.erase i.1, by rw [Finset.card_erase_of_mem i.2, hT'_card]; omega⟩)
    have hR : (Work.DSCOH.cechDiff (A := R) (n := n) (M := M) ℳ q y) T'
        = ∑ i ∈ T'.1.attach, G i := by
      rw [Work.DSCOH.cechDiff, LinearMap.pi_apply, Work.DSCOH.cechDiffComp,
        LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [hR]
    rw [show (∑ i ∈ T'.1.attach, G i) = ∑ i : ↥T'.1, G i from rfl]
    rw [show (∑ i : ↥T'.1, G i) = ∑ i' : Fin (q + 2), G (finTupEquiv (n := n) τ i') from
      (Equiv.sum_comp (finTupEquiv (n := n) τ) G).symm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    change (-1 : R) ^ (i' : ℕ) •
          (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ).res
            (Work.DSM5b.tupRng_del_subset i' τ.1)
            (y (incrSubEquiv (n := n) q ⟨Work.DSM5b.tupDel i' τ.1, τ.2.tupDel i'⟩))
        = (-1 : ℤ) ^ ((T'.1.filter fun j => j < (τ.1 i').down).card) •
          (Work.DSCOH.degPartRestrict (A := R) (n := n) (M := M) ℳ
            (Work.DSCOH.resAt (A := R) (n := n) (M := M)
              (Finset.erase_subset ((τ.1 i').down) T'.1))
            (fun x hx => Work.DSCOH.resAt_degZero (A := R) (n := n) (M := M) (ℳ := ℳ)
              (Finset.erase_subset ((τ.1 i').down) T'.1) x hx))
          (y ⟨T'.1.erase ((τ.1 i').down),
            by rw [Finset.card_erase_of_mem (hmem i'), hT'_card]; omega⟩)
    rw [show (T'.1.filter fun j => j < (τ.1 i').down).card = (i' : ℕ) from by
      rw [hT'_val]
      exact card_filter_image_down_lt τ.1 (fun a b h => τ.2 a b h) i']
    rw [negOne_zsmul_eq_smul (A := R)]
    congr 1
    apply Subtype.ext
    change Work.DSCOH.resAt (A := R) (n := n) (M := M)
          (Finset.image_subset_image (f := ULift.down) (Work.DSM5b.tupRng_del_subset i' τ.1))
          (y (incrSubEquiv (n := n) q ⟨Work.DSM5b.tupDel i' τ.1, τ.2.tupDel i'⟩)).1
        = Work.DSCOH.resAt (A := R) (n := n) (M := M)
          (Finset.erase_subset ((τ.1 i').down) T'.1)
          (y ⟨T'.1.erase ((τ.1 i').down),
            by rw [Finset.card_erase_of_mem (hmem i'), hT'_card]; omega⟩).1
    have hS : incrSubEquiv (n := n) q ⟨Work.DSM5b.tupDel i' τ.1, τ.2.tupDel i'⟩
        = ⟨T'.1.erase ((τ.1 i').down),
            by rw [Finset.card_erase_of_mem (hmem i'), hT'_card]; omega⟩ := by
      apply Subtype.ext
      rw [incrSubEquiv_apply_val]
      exact image_down_tupRng_tupDel τ.1 (incr_injective τ.2) i'
    exact resAt_val_eq (R := R) (M := M) (n := n) (ℳ := ℳ) (T := T'.1)
      (S₁ := incrSubEquiv (n := n) q ⟨Work.DSM5b.tupDel i' τ.1, τ.2.tupDel i'⟩)
      (S₂ := ⟨T'.1.erase ((τ.1 i').down),
        by rw [Finset.card_erase_of_mem (hmem i'), hT'_card]; omega⟩)
      hS
      (Finset.image_subset_image (f := ULift.down) (Work.DSM5b.tupRng_del_subset i' τ.1))
      (Finset.erase_subset ((τ.1 i').down) T'.1) y
  have hcochain : ∀ q : ℕ,
      ModuleCat.ofHom ((chartToStc (n := n) (R := R) ℳ q).toLinearMap) ≫
          (Work.DSM5b.stcComplex (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ)).d q (q + 1) =
        (Work.DSCOH.chartCech (A := R) (n := n) (M := M) ℳ).d q (q + 1) ≫
          ModuleCat.ofHom ((chartToStc (n := n) (R := R) ℳ (q + 1)).toLinearMap) := by
    intro q
    rw [Work.DSM5b.stcComplex_d, chartCech_d]
    erw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
    congr 1
    refine LinearMap.ext (fun y => ?_)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hcomm q y
  refine ⟨?_⟩
  let Ψ : Work.DSCOH.chartCech (A := R) (n := n) (M := M) ℳ ⟶
      Work.DSM5b.stcComplex (Work.DSM5b.HCF.pullCoeff (n := n) (R := R) ℳ) :=
    CochainComplex.ofHom
      (fun q => ModuleCat.ofHom ((chartToStc (n := n) (R := R) ℳ q).toLinearMap)) hcochain
  haveI hcomp : ∀ q : ℕ, IsIso (Ψ.f q) := fun q => by
    change IsIso (ModuleCat.ofHom ((chartToStc (n := n) (R := R) ℳ q).toLinearMap))
    exact (LinearEquiv.toModuleIso (chartToStc (n := n) (R := R) ℳ q)).isIso_hom
  haveI hΨ : IsIso Ψ := HomologicalComplex.Hom.isIso_of_components Ψ
  exact (asIso Ψ).symm

end Work.DSM5b.HCF
