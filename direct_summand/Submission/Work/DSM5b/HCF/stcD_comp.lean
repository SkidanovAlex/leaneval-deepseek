import Mathlib
import Submission.Work.DSM5b.HCF.Sorted

namespace Work.DSM5b.HCF

open Work.DSM5b

universe u

/-- The comparison map `toStc : Htc 𝒜 m → Stc 𝒜 m` (restriction of a cochain on all tuples to
the increasing ones) is surjective: any cochain on the increasing tuples can be extended to all
tuples by declaring it to vanish on the non-increasing ones. -/
private lemma toStc_surjective {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]
    [LinearOrder ι] (𝒜 : Work.DSM5b.CoeffSys R ι) (m : ℕ) :
    Function.Surjective (Work.DSM5b.toStc 𝒜 m) := by
  classical
  intro x
  refine ⟨fun τ => if h : Work.DSM5b.IsIncr τ then x ⟨τ, h⟩ else 0, ?_⟩
  funext τ
  rw [Work.DSM5b.toStc_apply]
  simpa using
    (dite_eq_left τ.2 :
      (if h : Work.DSM5b.IsIncr τ.1 then x ⟨τ.1, h⟩ else 0) = x ⟨τ.1, τ.2⟩)

theorem stcD_comp {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (𝒜 : Work.DSM5b.CoeffSys R ι) (m : ℕ) :
    (Work.DSM5b.stcD 𝒜 (m + 1)).comp (Work.DSM5b.stcD 𝒜 m) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := toStc_surjective 𝒜 m x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  -- `stcD` is the restriction of `htcD` along the surjective comparison map `toStc`
  have h1 := congrArg (fun f => f z) (Work.DSM5b.toStc_comm 𝒜 m)
  simp only [LinearMap.comp_apply] at h1
  have h2 := congrArg (fun f => f (Work.DSM5b.CoeffSys.htcD (𝒜 := 𝒜) m z))
    (Work.DSM5b.toStc_comm 𝒜 (m + 1))
  simp only [LinearMap.comp_apply] at h2
  have h3 : Work.DSM5b.CoeffSys.htcD (𝒜 := 𝒜) (m + 1)
      (Work.DSM5b.CoeffSys.htcD (𝒜 := 𝒜) m z) = 0 := by
    simpa using congrArg (fun f => f z) (Work.DSM5b.CoeffSys.htcD_comp (𝒜 := 𝒜) m)
  rw [h1, h2, h3]
  rfl

end Work.DSM5b.HCF
