import Mathlib
import Submission.Work.Smooth.OneManifold.Defs
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.Plane.Slicing

namespace Work.EpsW

open LeanEval.KnotTheory.PardonDistortion
open Set Function

noncomputable section

/-!
# Two arcs glued at a common endpoint are locally an arc

The helper development below constructs, from two injective continuous arcs
`f, g : [0,1] → ℝ³` meeting exactly in the single point `f 1 = g 0`, a
parametrisation (the "glued" map `glue f g`) of a neighbourhood of the joint
point.  Since `glue f g` is continuous and injective on the compact interval
`[-1/2, 1/2]`, it is a homeomorphism onto its image, and the trace of the
complement of `f '' [0,1/2] ∪ g '' [1/2,1]` is the homeomorphic image of the
open interval `(-1/2, 1/2) ≅ ℝ`.
-/

/-! ## The glued parametrisation -/

/-- The clamp of `f` to the whole line (constant outside `[0,1]`). -/
private def liftF (f : C(Work.Smooth.Plane.ArcInterval, R3)) : ℝ → R3 :=
  Set.IccExtend (show (0:ℝ) ≤ 1 by norm_num) f

private lemma liftF_of_mem (f : C(Work.Smooth.Plane.ArcInterval, R3)) {x : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) : liftF f x = f ⟨x, hx⟩ := Set.IccExtend_of_mem _ f hx

private lemma liftF_cont (f : C(Work.Smooth.Plane.ArcInterval, R3)) : Continuous (liftF f) :=
  f.continuous.comp continuous_projIcc

private lemma liftF_one (f : C(Work.Smooth.Plane.ArcInterval, R3)) : liftF f 1 = f 1 := by
  rw [liftF_of_mem f (by norm_num : (1:ℝ) ∈ Set.Icc 0 1)]
  exact congrArg f (Subtype.ext rfl)

private lemma liftF_zero (f : C(Work.Smooth.Plane.ArcInterval, R3)) : liftF f 0 = f 0 := by
  rw [liftF_of_mem f (by norm_num : (0:ℝ) ∈ Set.Icc 0 1)]
  exact congrArg f (Subtype.ext rfl)

/-- The two arcs glued at the parameter `0`: `t < 0` runs backwards along `f`, `t ≥ 0` runs
forwards along `g`. -/
private def glue (f g : C(Work.Smooth.Plane.ArcInterval, R3)) : ℝ → R3 :=
  Set.piecewise (Set.Iio (0:ℝ)) (fun t => liftF f (1 + t)) (fun t => liftF g t)

private lemma glue_of_neg (f g : C(Work.Smooth.Plane.ArcInterval, R3)) {t : ℝ} (ht : t < 0) :
    glue f g t = liftF f (1 + t) := Set.piecewise_eq_of_mem _ _ _ (by simpa using ht)

private lemma glue_of_nonneg (f g : C(Work.Smooth.Plane.ArcInterval, R3)) {t : ℝ} (ht : 0 ≤ t) :
    glue f g t = liftF g t := Set.piecewise_eq_of_notMem _ _ _ (by simpa using ht)

private lemma glue_cont (f g : C(Work.Smooth.Plane.ArcInterval, R3)) (hjoin : f 1 = g 0) :
    Continuous (glue f g) := by
  refine Continuous.piecewise ?_ ?_ ?_
  · intro a ha
    rw [frontier_Iio, mem_singleton_iff] at ha
    subst ha
    show liftF f (1 + 0) = liftF g 0
    rw [add_zero, liftF_one, liftF_zero]
    exact hjoin
  · exact (liftF_cont f).comp (continuous_const.add continuous_id)
  · exact liftF_cont g

/-- **The glued map is injective on `[-1/2, 1/2]`.** -/
private lemma glue_injOn {f g : C(Work.Smooth.Plane.ArcInterval, R3)}
    (hf : Function.Injective f) (hg : Function.Injective g) (hjoin : f 1 = g 0)
    (hdisj : Set.range f ∩ Set.range g = {f 1}) :
    Set.InjOn (glue f g) (Set.Icc (-(1/2)) (1/2)) := by
  intro s hs t ht hst
  rcases lt_or_ge s 0 with hsneg | hsnn
  · have hs1 : (1 + s) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [hs.1, hsneg]
    rcases lt_or_ge t 0 with htneg | htnn
    · have ht1 : (1 + t) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [ht.1, htneg]
      rw [glue_of_neg _ _ hsneg, glue_of_neg _ _ htneg, liftF_of_mem _ hs1,
        liftF_of_mem _ ht1] at hst
      have h2 : (1 + s) = (1 + t) := by simpa using congrArg Subtype.val (hf hst)
      linarith
    · have ht0 : t ∈ Set.Icc (0:ℝ) 1 := ⟨htnn, by linarith [ht.2]⟩
      rw [glue_of_neg _ _ hsneg, glue_of_nonneg _ _ htnn, liftF_of_mem _ hs1,
        liftF_of_mem _ ht0] at hst
      have hmem : f ⟨1 + s, hs1⟩ ∈ Set.range f ∩ Set.range g :=
        ⟨Set.mem_range.mpr ⟨⟨1 + s, hs1⟩, rfl⟩, Set.mem_range.mpr ⟨⟨t, ht0⟩, hst.symm⟩⟩
      rw [hdisj, mem_singleton_iff] at hmem
      have h1 : (1 + s) = 1 := by simpa using congrArg Subtype.val (hf hmem)
      have h2 : g ⟨t, ht0⟩ = g (0 : Work.Smooth.Plane.ArcInterval) := by
        rw [← hst, hmem]; exact hjoin
      have h3 : t = 0 := by simpa using congrArg Subtype.val (hg h2)
      linarith
  · have hs0 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hsnn, by linarith [hs.2]⟩
    rcases lt_or_ge t 0 with htneg | htnn
    · have ht1 : (1 + t) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith [ht.1, htneg]
      rw [glue_of_nonneg _ _ hsnn, glue_of_neg _ _ htneg, liftF_of_mem _ hs0,
        liftF_of_mem _ ht1] at hst
      have hmem : f ⟨1 + t, ht1⟩ ∈ Set.range f ∩ Set.range g :=
        ⟨Set.mem_range.mpr ⟨⟨1 + t, ht1⟩, rfl⟩, Set.mem_range.mpr ⟨⟨s, hs0⟩, hst⟩⟩
      rw [hdisj, mem_singleton_iff] at hmem
      have h1 : (1 + t) = 1 := by simpa using congrArg Subtype.val (hf hmem)
      have h2 : g ⟨s, hs0⟩ = g (0 : Work.Smooth.Plane.ArcInterval) := by
        rw [hst, hmem]; exact hjoin
      have h3 : s = 0 := by simpa using congrArg Subtype.val (hg h2)
      linarith
    · have ht0 : t ∈ Set.Icc (0:ℝ) 1 := ⟨htnn, by linarith [ht.2]⟩
      rw [glue_of_nonneg _ _ hsnn, glue_of_nonneg _ _ htnn, liftF_of_mem _ hs0,
        liftF_of_mem _ ht0] at hst
      exact congrArg Subtype.val (hg hst)

/-! ## Images of the lifted arcs -/

private lemma sub_Icc_half (s : ℝ) : s ∈ Set.Icc (0:ℝ) (1/2) → s ∈ Set.Icc (0:ℝ) 1 :=
  fun hs => ⟨hs.1, by linarith [hs.2]⟩

private lemma sub_Ioc_half (s : ℝ) : s ∈ Set.Ioc ((1/2):ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 :=
  fun hs => ⟨by linarith [hs.1], hs.2⟩

private lemma sub_Ico_zero_half (s : ℝ) : s ∈ Set.Ico (0:ℝ) (1/2) → s ∈ Set.Icc (0:ℝ) 1 :=
  fun hs => ⟨hs.1, by linarith [hs.2]⟩

private lemma sub_half_Icc (s : ℝ) : s ∈ Set.Icc ((1/2):ℝ) 1 → s ∈ Set.Icc (0:ℝ) 1 :=
  fun hs => ⟨by linarith [hs.1], hs.2⟩

private lemma sub_Ioo (s : ℝ) : s ∈ Set.Ioo (-(1/2)) (1/2) → s ∈ Set.Icc (-(1/2)) (1/2) :=
  fun hs => ⟨le_of_lt hs.1, le_of_lt hs.2⟩

/-- Membership of a point of `ℝ³` in the image of a lifted arc over a set of parameters
contained in `[0,1]`. -/
private lemma mem_liftF_image {f : C(Work.Smooth.Plane.ArcInterval, R3)} {S : Set ℝ}
    (hS : S ⊆ Set.Icc (0:ℝ) 1) {y : R3} :
    y ∈ liftF f '' S ↔ ∃ u : ↥(Set.Icc (0:ℝ) 1), (u : ℝ) ∈ S ∧ f u = y := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hS hs⟩, hs, (liftF_of_mem f (hS hs)).symm⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(u : ℝ), hu, by rw [liftF_of_mem f u.2]⟩

/-! ## The trace of the complement of a half of each arc -/

/-- The complement of `f '' [0,1/2] ∪ g '' [1/2,1]` meets the arc `f` exactly in `f '' (1/2,1]`. -/
private lemma compl_inter_range_f {f g : C(Work.Smooth.Plane.ArcInterval, R3)}
    (hf : Function.Injective f) (hg : Function.Injective g) (hjoin : f 1 = g 0)
    (hdisj : Set.range f ∩ Set.range g = {f 1}) :
    ((liftF f '' Set.Icc (0:ℝ) (1/2) ∪ liftF g '' Set.Icc ((1/2):ℝ) 1)ᶜ) ∩ Set.range f
      = liftF f '' Set.Ioc ((1/2):ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨hyO, hyf⟩
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hyO
    obtain ⟨hySf, -⟩ := hyO
    obtain ⟨u, rfl⟩ := hyf
    rw [mem_liftF_image (f := f) (S := Set.Icc (0:ℝ) (1/2)) sub_Icc_half] at hySf
    refine (mem_liftF_image (f := f) (S := Set.Ioc ((1/2):ℝ) 1) sub_Ioc_half).mpr
      ⟨u, ⟨?_, u.2.2⟩, rfl⟩
    by_contra h
    exact hySf ⟨u, ⟨u.2.1, not_lt.mp h⟩, rfl⟩
  · intro hy
    rw [mem_liftF_image (f := f) (S := Set.Ioc ((1/2):ℝ) 1) sub_Ioc_half] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    refine ⟨?_, Set.mem_range.mpr ⟨u, rfl⟩⟩
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [mem_liftF_image (f := f) (S := Set.Icc (0:ℝ) (1/2)) sub_Icc_half]
      rintro ⟨u', hu', hfu⟩
      have h3 : (u' : ℝ) = (u : ℝ) := congrArg Subtype.val (hf hfu)
      linarith [hu'.2, hu.1, h3]
    · rw [mem_liftF_image (f := g) (S := Set.Icc ((1/2):ℝ) 1) sub_half_Icc]
      rintro ⟨u', hu', hgu⟩
      have hmem : f u ∈ Set.range f ∩ Set.range g :=
        ⟨Set.mem_range.mpr ⟨u, rfl⟩, Set.mem_range.mpr ⟨u', hgu⟩⟩
      rw [hdisj, mem_singleton_iff] at hmem
      have h3 : g u' = g (0 : Work.Smooth.Plane.ArcInterval) := by
        rw [hgu, hmem]; exact hjoin
      have h4 : (u' : ℝ) = 0 := congrArg Subtype.val (hg h3)
      linarith [hu'.1, h4]

/-- The complement of `f '' [0,1/2] ∪ g '' [1/2,1]` meets the arc `g` exactly in `g '' [0,1/2)`. -/
private lemma compl_inter_range_g {f g : C(Work.Smooth.Plane.ArcInterval, R3)}
    (hf : Function.Injective f) (hg : Function.Injective g) (_hjoin : f 1 = g 0)
    (hdisj : Set.range f ∩ Set.range g = {f 1}) :
    ((liftF f '' Set.Icc (0:ℝ) (1/2) ∪ liftF g '' Set.Icc ((1/2):ℝ) 1)ᶜ) ∩ Set.range g
      = liftF g '' Set.Ico (0:ℝ) (1/2) := by
  ext y
  constructor
  · rintro ⟨hyO, hyg⟩
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hyO
    obtain ⟨-, hySg⟩ := hyO
    obtain ⟨u, rfl⟩ := hyg
    rw [mem_liftF_image (f := g) (S := Set.Icc ((1/2):ℝ) 1) sub_half_Icc] at hySg
    refine (mem_liftF_image (f := g) (S := Set.Ico (0:ℝ) (1/2)) sub_Ico_zero_half).mpr
      ⟨u, ⟨u.2.1, ?_⟩, rfl⟩
    by_contra h
    exact hySg ⟨u, ⟨not_lt.mp h, u.2.2⟩, rfl⟩
  · intro hy
    rw [mem_liftF_image (f := g) (S := Set.Ico (0:ℝ) (1/2)) sub_Ico_zero_half] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    refine ⟨?_, Set.mem_range.mpr ⟨u, rfl⟩⟩
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · rw [mem_liftF_image (f := f) (S := Set.Icc (0:ℝ) (1/2)) sub_Icc_half]
      rintro ⟨u', hu', hfu⟩
      have hmem : f u' ∈ Set.range f ∩ Set.range g :=
        ⟨Set.mem_range.mpr ⟨u', rfl⟩, Set.mem_range.mpr ⟨u, hfu.symm⟩⟩
      rw [hdisj, mem_singleton_iff] at hmem
      have h3 : (u' : ℝ) = 1 := congrArg Subtype.val (hf hmem)
      linarith [hu'.2, h3]
    · rw [mem_liftF_image (f := g) (S := Set.Icc ((1/2):ℝ) 1) sub_half_Icc]
      rintro ⟨u', hu', hgu⟩
      have h3 : (u' : ℝ) = (u : ℝ) := congrArg Subtype.val (hg hgu)
      linarith [hu'.1, hu.2, h3]

/-- The glued map parametrises the union of `f '' (1/2,1]` and `g '' [0,1/2)` over the open
interval `(-1/2,1/2)`. -/
private lemma glue_image_Ioo {f g : C(Work.Smooth.Plane.ArcInterval, R3)} (hjoin : f 1 = g 0) :
    glue f g '' Set.Ioo (-(1/2)) (1/2)
      = liftF f '' Set.Ioc ((1/2):ℝ) 1 ∪ liftF g '' Set.Ico (0:ℝ) (1/2) := by
  have hF1 : liftF f 1 = liftF g 0 := by rw [liftF_one, liftF_zero]; exact hjoin
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases lt_or_ge t 0 with htneg | htge
    · left
      have h₁ : (1 + t) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.1], by linarith [htneg]⟩
      have h₂ : (1 + t) ∈ Set.Ioc ((1/2):ℝ) 1 := ⟨by linarith [ht.1], by linarith [htneg]⟩
      refine (mem_liftF_image (f := f) (S := Set.Ioc ((1/2):ℝ) 1) sub_Ioc_half).mpr
        ⟨⟨1 + t, h₁⟩, h₂, ?_⟩
      rw [glue_of_neg _ _ htneg, liftF_of_mem f h₁]
    · right
      have h₁ : t ∈ Set.Icc (0:ℝ) 1 := ⟨htge, by linarith [ht.2]⟩
      have h₂ : t ∈ Set.Ico (0:ℝ) (1/2) := ⟨htge, ht.2⟩
      refine (mem_liftF_image (f := g) (S := Set.Ico (0:ℝ) (1/2)) sub_Ico_zero_half).mpr
        ⟨⟨t, h₁⟩, h₂, ?_⟩
      rw [glue_of_nonneg _ _ htge, liftF_of_mem g h₁]
  · rintro (hy | hy)
    · rw [mem_liftF_image (f := f) (S := Set.Ioc ((1/2):ℝ) 1) sub_Ioc_half] at hy
      obtain ⟨u, hu, huy⟩ := hy
      have huIcc : (u : ℝ) ∈ Set.Icc (0:ℝ) 1 := sub_Ioc_half (u:ℝ) hu
      rcases eq_or_lt_of_le hu.2 with h1 | h1
      · refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
        have hu1 : u = 1 := Subtype.ext h1
        rw [glue_of_nonneg _ _ le_rfl, ← hF1, ← huy, hu1, liftF_one]
      · have ht0 : (u : ℝ) - 1 < 0 := by linarith [h1]
        have ht1 : -(1/2) < (u:ℝ) - 1 := by linarith [hu.1]
        have ht2 : (u:ℝ) - 1 < 1/2 := by linarith
        refine ⟨(u : ℝ) - 1, ⟨ht1, ht2⟩, ?_⟩
        rw [glue_of_neg _ _ ht0, show 1 + ((u:ℝ) - 1) = (u:ℝ) by ring, liftF_of_mem f huIcc]
        exact huy
    · rw [mem_liftF_image (f := g) (S := Set.Ico (0:ℝ) (1/2)) sub_Ico_zero_half] at hy
      obtain ⟨u, hu, huy⟩ := hy
      have huIcc : (u : ℝ) ∈ Set.Icc (0:ℝ) 1 := sub_Ico_zero_half (u:ℝ) hu
      rcases eq_or_lt_of_le hu.1 with h1 | h1
      · refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
        have hu1 : u = 0 := Subtype.ext h1.symm
        rw [glue_of_nonneg _ _ le_rfl, liftF_zero, ← huy, hu1]
      · have ht1 : -(1/2) < (u:ℝ) := by linarith [h1]
        have ht2 : (u:ℝ) < 1/2 := hu.2
        refine ⟨(u : ℝ), ⟨ht1, ht2⟩, ?_⟩
        rw [glue_of_nonneg _ _ h1.le, liftF_of_mem g huIcc]
        exact huy

/-! ## A continuous injection on a compact interval is a homeomorphism onto its image -/

/-- **The parametrised piece `P '' J` of a compact arc is homeomorphic to `J`.** -/
private noncomputable def imageHomeomorph {K J : Set ℝ} (hJK : J ⊆ K) (hK : IsCompact K)
    {P : ℝ → R3} (hcont : Continuous P) (hinj : Set.InjOn P K) :
    ↥J ≃ₜ ↥(P '' J) := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let φ : ↥K → ↥(P '' K) := fun t => ⟨P t, ⟨t, t.2, rfl⟩⟩
  have hφcont : Continuous φ := Continuous.subtype_mk (hcont.comp continuous_subtype_val) _
  have hφinj : Function.Injective φ :=
    fun s t hst => Subtype.ext (hinj s.2 t.2 (congrArg Subtype.val hst))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩; obtain ⟨t, ht, hte⟩ := hy; exact ⟨⟨t, ht⟩, Subtype.ext hte⟩
  let e : ↥K ≃ₜ ↥(P '' K) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩) hφcont
  have he : ∀ t : ↥K, ((e t : ↥(P '' K)) : R3) = P t := fun t => rfl
  have he_symm : ∀ z : ↥(P '' K), P ((e.symm z).1) = (z : R3) := by
    intro z
    have h : ((e (e.symm z) : ↥(P '' K)) : R3) = P ((e.symm z).1) := he _
    rw [Homeomorph.apply_symm_apply] at h
    exact h.symm
  have hmemK : ∀ z : ↥(P '' J), (z : R3) ∈ P '' K := by
    intro z; rcases z.2 with ⟨t, ht, hte⟩; exact ⟨t, hJK ht, hte⟩
  let mkK : ↥(P '' J) → ↥(P '' K) := fun z => ⟨(z : R3), hmemK z⟩
  have hmemJ : ∀ z : ↥(P '' J), (e.symm (mkK z)).1 ∈ J := by
    intro z
    have h1 := he_symm (mkK z)
    rcases z.2 with ⟨t, ht, hte⟩
    have h2 : t = (e.symm (mkK z)).1 :=
      hinj (hJK ht) (e.symm (mkK z)).2 (by rw [hte, h1])
    rwa [← h2]
  refine { toFun := fun s => ⟨P s.1, ⟨s.1, s.2, rfl⟩⟩
           invFun := fun z => ⟨(e.symm (mkK z)).1, hmemJ z⟩
           left_inv := ?_
           right_inv := ?_
           continuous_toFun := Continuous.subtype_mk (hcont.comp continuous_subtype_val) _
           continuous_invFun := Continuous.subtype_mk
             (continuous_subtype_val.comp (e.symm.continuous.comp
               (Continuous.subtype_mk continuous_subtype_val hmemK))) _ }
  · intro s
    apply Subtype.ext
    show ((e.symm (mkK ⟨P s.1, ⟨s.1, s.2, rfl⟩⟩)).1 : ℝ) = (s.1 : ℝ)
    have h1 : e ⟨s.1, hJK s.2⟩ = mkK ⟨P s.1, ⟨s.1, s.2, rfl⟩⟩ := Subtype.ext (he _)
    rw [← h1, Homeomorph.symm_apply_apply]
  · intro z
    apply Subtype.ext
    exact he_symm (mkK z)

/-- `ℝ ≃ₜ (-1/2, 1/2)` (a rescaled arctangent). -/
private noncomputable def homeoJ : ℝ ≃ₜ ↥(Set.Ioo ((-(1/2) : ℝ)) (1/2)) :=
  (Work.Smooth.OneManifold.homeomorphIooCentre 0 (1/2) (by norm_num)).trans
    (Homeomorph.setCongr (by
      ext x
      simp only [Set.mem_Ioo]
      constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩))

/-- `ℝ` is locally an arc. -/
private theorem isLocallyArc_real : Work.Smooth.SphereJordan.IsLocallyArc ℝ := fun x =>
  ⟨{ V := Set.univ
     isOpen_V := isOpen_univ
     mem_V := Set.mem_univ x
     homeo := (Homeomorph.addRight x).trans (Homeomorph.Set.univ ℝ).symm
     homeo_zero := by
       apply Subtype.ext
       simp [Homeomorph.addRight] }⟩

open LeanEval.KnotTheory.PardonDistortion in
/-- **Two injective arcs of `ℝ³` meeting exactly at a common endpoint form a topological arc locally at that point.**  If `f`, `g` are injective continuous maps of the unit interval with `f 1 = g 0` and `Set.range f ∩ Set.range g = {f 1}`, then there is an open neighbourhood `O` of the joint point `f 1` whose trace on `Set.range f ∪ Set.range g` is a topological `1`-manifold.  Suggested witness: `O := (f '' [0,1/2] ∪ g '' [1/2,1])ᶜ`, so that `O ∩ (Set.range f ∪ Set.range g) = f '' (1/2,1] ∪ g '' [0,1/2)` is the image of the glued parametrisation `t ↦ (if t < 0 then f (1+t) else g t)` on `(-1/2, 1/2)`, which is injective and (by compactness of `[-1/2,1/2]` and `Continuous.homeoOfEquivCompactToT2`) a homeomorphism onto its image. -/
theorem localArc_gluedPair {f g : C(Work.Smooth.Plane.ArcInterval, R3)}
    (hf : Function.Injective f) (hg : Function.Injective g) (hjoin : f 1 = g 0)
    (hdisj : Set.range f ∩ Set.range g = {f 1}) :
    ∃ O : Set R3, IsOpen O ∧ f 1 ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean (O ∩ (Set.range f ∪ Set.range g)) := by
  set O : Set R3 :=
    (liftF f '' Set.Icc (0:ℝ) (1/2) ∪ liftF g '' Set.Icc ((1/2):ℝ) 1)ᶜ with hOdef
  have hOopen : IsOpen O := by
    rw [hOdef, isOpen_compl_iff]
    exact ((isCompact_Icc.image (liftF_cont f)).union
      (isCompact_Icc.image (liftF_cont g))).isClosed
  have hf1O : f 1 ∈ O := by
    rw [hOdef, Set.mem_compl_iff, Set.mem_union, not_or]
    constructor
    · rw [mem_liftF_image (S := Set.Icc (0:ℝ) (1/2)) sub_Icc_half]
      rintro ⟨u, hu, hfu⟩
      have h1 : (u:ℝ) = 1 := congrArg Subtype.val (hf hfu)
      linarith [hu.2, h1]
    · rw [mem_liftF_image (f := g) (S := Set.Icc ((1/2):ℝ) 1) sub_half_Icc]
      rintro ⟨u, hu, hgu⟩
      have h2 : g u = g (0 : Work.Smooth.Plane.ArcInterval) := by rw [hgu, hjoin]
      have h1 : (u:ℝ) = 0 := congrArg Subtype.val (hg h2)
      linarith [hu.1, h1]
  refine ⟨O, hOopen, hf1O, ?_⟩
  have hT : O ∩ (Set.range f ∪ Set.range g) = glue f g '' Set.Ioo (-(1/2)) (1/2) := by
    rw [hOdef, Set.inter_union_distrib_left, compl_inter_range_f hf hg hjoin hdisj,
      compl_inter_range_g hf hg hjoin hdisj, glue_image_Ioo hjoin]
  have hchain : ℝ ≃ₜ ↥(O ∩ (Set.range f ∪ Set.range g)) :=
    (homeoJ.trans (imageHomeomorph (K := Set.Icc (-(1/2)) (1/2)) (J := Set.Ioo (-(1/2)) (1/2))
        (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩) isCompact_Icc (P := glue f g)
        (glue_cont f g hjoin) (glue_injOn hf hg hjoin hdisj))).trans
      (Homeomorph.setCongr hT.symm)
  exact Work.Smooth.OneManifold.isLocallyArc_of_homeomorph hchain isLocallyArc_real

end

end Work.EpsW
