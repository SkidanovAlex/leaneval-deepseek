import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PGL.centralizer_fourGroup

open scoped MatrixGroups

namespace Work.L2F.PSL

/-- The natural injective map `PSL(2,F) →* PGL(2,F)` (the inclusion of `SL(2,F)/Z`
into `GL(2,F)/Z`). -/
abbrev pslToPGL (F : Type*) [Field F] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →* Matrix.ProjGenLinGroup (Fin 2) F :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL

lemma pslToPGL_injective (F : Type*) [Field F] : Function.Injective (pslToPGL F) :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

/-- `V.map φ` is a four-group whenever `V` is and `φ` is injective. -/
lemma isFourGroup_map_of_injective {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) {V : Subgroup G} (hV : Work.L2F.IsFourGroup V) :
    Work.L2F.IsFourGroup (V.map φ) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hφ, hV.1]
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_pow, hV.2 u hu, map_one]

/-- The centralizer of a subgroup commutes with taking `comap` along an injective monoid
homomorphism. -/
lemma centralizer_comap_eq_of_injective {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) (V : Subgroup G) :
    (Subgroup.centralizer (V.map φ : Set H)).comap φ = Subgroup.centralizer (V : Set G) := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx u hu
    apply hφ
    rw [map_mul, map_mul]
    exact hx (φ u) ⟨u, hu, rfl⟩
  · intro hx y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, hx u hu, map_mul]

/-- Four-subgroups are self-centralizing in `PSL(2,F)` (`F` finite, odd characteristic).
Proof: `V ≤ PSL(2,F) ≤ PGL(2,F)` via `Matrix.ProjectiveSpecialLinearGroup.toPGL` (injective), and
`C_{PSL}(V) = C_{PGL}(V.map toPGL) ⊓ PSL(2,F) = V.map toPGL ⊓ PSL(2,F) = V`, using
`Work.L2F.PGL.centralizer_fourGroup` for the middle equality and `Nat.card (V.map toPGL) = 4`. -/
theorem centralizer_fourGroup_psl (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (V : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) (hV : Work.L2F.IsFourGroup V) :
    Subgroup.centralizer (V : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = V := by
  have hinj : Function.Injective (pslToPGL F) := pslToPGL_injective F
  have hV' : Work.L2F.IsFourGroup (V.map (pslToPGL F)) :=
    isFourGroup_map_of_injective (pslToPGL F) hinj hV
  have hcent : (Subgroup.centralizer (V.map (pslToPGL F) :
      Set (Matrix.ProjGenLinGroup (Fin 2) F))).comap (pslToPGL F) =
      Subgroup.centralizer (V : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
    centralizer_comap_eq_of_injective (pslToPGL F) hinj V
  have hpgl : Subgroup.centralizer (V.map (pslToPGL F) :
      Set (Matrix.ProjGenLinGroup (Fin 2) F)) = V.map (pslToPGL F) :=
    Work.L2F.PGL.centralizer_fourGroup F h2 (V.map (pslToPGL F)) hV'
  rw [← hcent, hpgl, Subgroup.comap_map_eq_self_of_injective hinj V]

end Work.L2F.PSL
