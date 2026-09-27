import Mathlib
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.coarseInverse
import Submission.Work.Mostow.BdExt.bdMapCmp
import Submission.Work.Mostow.BdExt.bdMapCont
import Submission.Work.BdExt.bdMapLeftInv
import Submission.Work.BdExt.bdMapRightInv

/-!
# `bdMapBij`: the boundary extension of a quasi-isometry is a bijection

For a quasi-isometry `Φ` of `ℍⁿ` with constants `K, C` (`K ≥ 1`, `C ≥ 0`), a lower bound with the
same constants and coarse surjectivity with constant `C`, the boundary extension `bdMap n Φ` maps
`Sph n` bijectively onto `Sph n`.

The proof uses the coarse inverse `Ψ` of `Φ` (`coarseInverse`), which satisfies
`hdist (Ψ (Φ u)) u ≤ K C + C`, `hdist (Φ (Ψ u)) u ≤ C` and is itself a quasi-isometry.  The two
composition identities

* `bdMap n Ψ (bdMap n Φ ξ) = ξ`  (`Work.BdExt.bdMapLeftInv`),
* `bdMap n Φ (bdMap n Ψ η) = η`  (`Work.BdExt.bdMapRightInv`),

are the lemmas `Work.BdExt.bdMapLeftInv` / `Work.BdExt.bdMapRightInv` (modules
`Submission.Work.BdExt.bdMapLeftInv`, `Submission.Work.BdExt.bdMapRightInv`), proved from the
detection principle `bdMapDetect`, the bounded-distance comparison `closeSeq` and continuity of
the boundary maps.  Here we supply the continuity of `bdMap n Φ` and of `bdMap n Ψ`
(`bdMapCmp` + `bdMapCont`, with the quasi-isometry constants of the coarse inverse `Ψ`
assembled explicitly below), and derive injectivity and surjectivity of `bdMap n Φ`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow Filter

noncomputable section

/-- **The boundary extension of a quasi-isometry is a bijection of the boundary sphere.** -/
theorem bdMapBij (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ : Submission.Mostow.E n → Submission.Mostow.E n) (K C : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hup : ∀ u v, Submission.Mostow.hdist (Φ u) (Φ v) ≤ K * Submission.Mostow.hdist u v + C)
    (hlow : ∀ u v, Submission.Mostow.hdist u v ≤ K * Submission.Mostow.hdist (Φ u) (Φ v) + C)
    (hsurj : ∀ w, ∃ u, Submission.Mostow.hdist (Φ u) w ≤ C)
    (hdetect : ∀ (Ψ : Submission.Mostow.E n → Submission.Mostow.E n) (K' C' : ℝ), 1 ≤ K' → 0 ≤ C' →
        (∀ u v, Submission.Mostow.hdist (Ψ u) (Ψ v) ≤ K' * Submission.Mostow.hdist u v + C') →
        (∀ u v, Submission.Mostow.hdist u v ≤ K' * Submission.Mostow.hdist (Ψ u) (Ψ v) + C') →
        ContinuousOn (fun ξ : Submission.Mostow.E n => Work.Mostow.BdExt.bdMap n Ψ ξ)
          (Submission.Mostow.Sph n) →
        ∀ (z : ℕ → Submission.Mostow.E n) (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
          Filter.Tendsto (fun k => Work.Mostow.BdExt.dirv (z k)) Filter.atTop (nhds ξ) →
          Filter.Tendsto (fun k => Work.Mostow.BdExt.lvl (z k)) Filter.atTop Filter.atTop →
          Filter.Tendsto (fun k => Work.Mostow.BdExt.dirv (Ψ (z k))) Filter.atTop
            (nhds (Work.Mostow.BdExt.bdMap n Ψ ξ))) :
    Set.BijOn (fun ξ : Submission.Mostow.E n => Work.Mostow.BdExt.bdMap n Φ ξ)
      (Submission.Mostow.Sph n) (Submission.Mostow.Sph n)  := by
  classical
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  -- continuity of the boundary map of `Φ`
  obtain ⟨T₀, C₆, hT₀, hC₆, hcmp⟩ := bdMapCmp n hI Φ K C hK hC hup hlow
  have hcontΦ : ContinuousOn (fun ξ : E n => bdMap n Φ ξ) (Sph n) :=
    bdMapCont n hI Φ K C T₀ C₆ hKpos hT₀ hC₆ hcmp
  -- a coarse inverse `Ψ` of `Φ`, with the estimates of `coarseInverse`
  obtain ⟨Ψ, hΦΨ, hΨΦ, hΨup, hΨsurj⟩ := coarseInverse n hI Φ K C hK hC hup hlow hsurj
  -- the lower quasi-isometry bound for `Ψ`
  have hΨlow : ∀ u v, hdist u v ≤ K * hdist (Ψ u) (Ψ v) + 3 * C := by
    intro u v
    have h1 : hdist u (Φ (Ψ u)) ≤ C := by
      rw [hI.2.1 u (Φ (Ψ u))]
      exact hΦΨ u
    have h2 : hdist (Φ (Ψ v)) v ≤ C := hΦΨ v
    have h3 : hdist u v ≤ hdist u (Φ (Ψ u)) + hdist (Φ (Ψ u)) (Φ (Ψ v)) + hdist (Φ (Ψ v)) v := by
      have t1 : hdist u (Φ (Ψ v)) ≤ hdist u (Φ (Ψ u)) + hdist (Φ (Ψ u)) (Φ (Ψ v)) :=
        hI.2.2.2.1 u (Φ (Ψ u)) (Φ (Ψ v))
      have t2 : hdist u v ≤ hdist u (Φ (Ψ v)) + hdist (Φ (Ψ v)) v :=
        hI.2.2.2.1 u (Φ (Ψ v)) v
      linarith
    have h4 : hdist (Φ (Ψ u)) (Φ (Ψ v)) ≤ K * hdist (Ψ u) (Ψ v) + C := hup (Ψ u) (Ψ v)
    linarith
  -- a single pair of constants `K, Cp` for `Ψ`
  set Cp : ℝ := 2 * K * C + C + 3 * C with hCpdef
  have hCpnn : 0 ≤ Cp := by
    rw [hCpdef]
    have h1 : 0 ≤ K * C := mul_nonneg hK0 hC
    linarith
  have hupΨ : ∀ u v, hdist (Ψ u) (Ψ v) ≤ K * hdist u v + Cp := by
    intro u v
    have h := hΨup u v
    have hle : 2 * K * C + C ≤ Cp := by
      rw [hCpdef]
      linarith [mul_nonneg hK0 hC]
    linarith
  have hlowΨ : ∀ u v, hdist u v ≤ K * hdist (Ψ u) (Ψ v) + Cp := by
    intro u v
    have h := hΨlow u v
    have hle : 3 * C ≤ Cp := by
      rw [hCpdef]
      linarith [mul_nonneg hK0 hC]
    linarith
  -- continuity of the boundary map of `Ψ`
  obtain ⟨T₁, C₇, hT₁, hC₇, hcmpΨ⟩ := bdMapCmp n hI Ψ K Cp hK hCpnn hupΨ hlowΨ
  have hcontΨ : ContinuousOn (fun ξ : E n => bdMap n Ψ ξ) (Sph n) :=
    bdMapCont n hI Ψ K Cp T₁ C₇ hKpos hT₁ hC₇ hcmpΨ
  -- the two composition identities
  have hKC : 0 ≤ K * C + C := by
    have h1 : 0 ≤ K * C := mul_nonneg hK0 hC
    linarith
  have hleft : ∀ (η : E n), η ∈ Sph n → bdMap n Ψ (bdMap n Φ η) = η :=
    fun η hη => Work.BdExt.bdMapLeftInv n hI Φ Ψ K C K Cp (K * C + C) hK hC hK hCpnn hKC
      hup hlow hupΨ hlowΨ (fun u => hΨΦ u) hcontΨ η hη
  have hright : ∀ (η : E n), η ∈ Sph n → bdMap n Φ (bdMap n Ψ η) = η :=
    fun η hη => Work.BdExt.bdMapRightInv n hI Φ Ψ K C K Cp C hK hC hK hCpnn hC
      hup hlow hupΨ hlowΨ (fun u => hΦΨ u) hcontΦ η hη
  refine ⟨?_, ?_, ?_⟩
  · intro η hη
    exact (bdMap_spec n hI Φ K C hK hC hup hlow η hη).1
  · intro ξ hξ ξ' hξ' heq
    have h := congrArg (fun y => bdMap n Ψ y) heq
    rw [hleft ξ hξ, hleft ξ' hξ'] at h
    exact h
  · intro η hη
    exact ⟨bdMap n Ψ η, (bdMap_spec n hI Ψ K Cp hK hCpnn hupΨ hlowΨ η hη).1, hright η hη⟩

end

end Work.Mostow.BdExt
