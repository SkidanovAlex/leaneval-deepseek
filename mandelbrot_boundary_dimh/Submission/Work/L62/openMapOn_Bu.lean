import Mathlib
import Submission.Work.L62.l62c_mid

namespace Work.L62

/-- **The lifted horn map `d.E` is open on the upper horn `hd.Bu`.**  `d.E : ℂ → ℂ` is `Φ ∘ φ`
(`ParabData.E`), holomorphic on the open connected set `hd.Bu` (`Work.L62.differentiableOn_E_Bu`,
`hd.Bu_open`, `hd.Bu_conn`) and surjective onto `ℂ` (`hd.surj_u`), hence not constant, so — being
holomorphic on a preconnected open set — it maps open subsets of `hd.Bu` to open subsets of `ℂ`
(`AnalyticOnNhd.is_constant_or_isOpen`).  This is the local surjectivity of `d.E` used by
`Work.L62.head_anchor`. -/
theorem openMapOn_Bu {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {s : Set ℂ} (hs : s ⊆ hd.Bu) (hso : IsOpen s) :
    IsOpen (d.E '' s) := by
  -- `d.E` is analytic on the open horn `hd.Bu`, which is connected, hence preconnected.
  rcases (AnalyticOnNhd.is_constant_or_isOpen
      ((differentiableOn_E_Bu d hd).analyticOnNhd hd.Bu_open)
      hd.Bu_conn.isPreconnected) with ⟨w, hw⟩ | hop
  · -- The constant case is impossible: `d.E` is surjective onto `ℂ` (`hd.surj_u`).
    exfalso
    obtain ⟨z, hz, hzE⟩ := hd.surj_u (w + 1)
    have h1 : d.E z = w := hw z hz
    have : w + 1 = w := by rw [← hzE, h1]
    exact one_ne_zero (by linear_combination this)
  · -- Otherwise `d.E` is an open map on `hd.Bu`; restrict along `s ⊆ hd.Bu`.
    exact hop s hs hso

end Work.L62
