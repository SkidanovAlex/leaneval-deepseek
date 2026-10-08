import Mathlib
import Submission.Work.BG.Glauberman

namespace Work.BG

/-- **BG-L1 (a central involution of the image).**  If `φ(S) ≠ 1` for a finite 2-group `S`,
then some `φ s₀` is an involution commuting with every `φ s`.

The proof: the image `H = φ.range` is a finite nontrivial 2-group, so its centre `Z(H)` is
nontrivial (`IsPGroup.center_nontrivial`); `Z(H)` is again a finite 2-group, hence its cardinal
is a positive power of `2`, so Cauchy's theorem produces `z ∈ Z(H)` of order `2`.  Lifting `z`
back to `S` gives the desired `s₀`. -/
theorem centralInvolution : Work.BG.CentralInvolutionProp := by
  intro S U _ _ _ hS φ hφ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- The image `H = φ.range` is finite, and a nontrivial 2-group.
  let f : S →* ↥(φ.range) := φ.codRestrict φ.range (fun s => MonoidHom.mem_range.mpr ⟨s, rfl⟩)
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp h.2
    exact ⟨s, Subtype.ext hs⟩
  haveI : Finite ↥(φ.range) := Finite.of_surjective f hf
  have hHp : IsPGroup 2 ↥(φ.range) := hS.of_surjective f hf
  haveI : Nontrivial ↥(φ.range) := (Subgroup.nontrivial_iff_ne_bot _).mpr hφ
  -- Its centre is a nontrivial finite 2-group.
  have hZnt : Nontrivial ↥(Subgroup.center ↥(φ.range)) := hHp.center_nontrivial
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥(φ.range)) := hHp.to_subgroup _
  obtain ⟨n, hnpos, hcard⟩ := (IsPGroup.nontrivial_iff_card hZ).mp hZnt
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥(φ.range)) :=
    hcard ▸ dvd_pow_self 2 hnpos.ne'
  letI : Fintype ↥(Subgroup.center ↥(φ.range)) := Fintype.ofFinite _
  have hdvd' : 2 ∣ Fintype.card ↥(Subgroup.center ↥(φ.range)) := by
    rw [Fintype.card_eq_nat_card]; exact hdvd
  -- Cauchy's theorem yields a central element of order `2`.
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card 2 hdvd'
  obtain ⟨s₀, hs₀⟩ := MonoidHom.mem_range.mp z.1.2
  have hz2 : z * z = 1 := by rw [← pow_two, ← hzord]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by rintro rfl; simp at hzord
  have hval2 : (z : MulAut U) * (z : MulAut U) = 1 := by
    have := congrArg (fun w : ↥(Subgroup.center ↥(φ.range)) => (w : MulAut U)) hz2
    simpa using this
  have hval1 : (z : MulAut U) ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext (Subtype.ext h))
  have hcomm : ∀ s : S, φ s * (z : MulAut U) = (z : MulAut U) * φ s := by
    intro s
    have :=
      Subgroup.mem_center_iff.mp z.2 (⟨φ s, MonoidHom.mem_range.mpr ⟨s, rfl⟩⟩ : ↥(φ.range))
    simpa using congrArg Subtype.val this
  exact ⟨s₀, by rw [hs₀]; exact hval1, by rw [hs₀]; exact hval2,
    by intro s; rw [hs₀]; exact hcomm s⟩

end Work.BG
