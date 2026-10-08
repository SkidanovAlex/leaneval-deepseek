import Mathlib
import Submission.Work.Grun.Basic
import Submission.Work.Grun.Diag
import Submission.Work.Grun.Hyp
import Submission.Work.Grun.theta_diagFactor_conj
import Submission.Work.Grun.prod_diagFactor_eq
import Submission.Work.NPC.Frobenius.exists_conj_le_of_relIndex_coprime

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Grun

/-- A `p`-element `v` of `H` is conjugate in `H` into the Sylow `p`-subgroup `P ≤ H`: `⟨v⟩` is a
`p`-group, hence lies in a Sylow `p`-subgroup `Q` of `H`; `P` is also a Sylow `p`-subgroup of `H`
(its index in `H` is prime to `p`), and all Sylow `p`-subgroups of `H` are `H`-conjugate. -/
theorem exists_conj_mem_of_pow_eq_one {G : Type*} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) {v : G} (hv : v ∈ H)
    (k : ℕ) (hvk : v ^ p ^ k = 1) :
    ∃ c ∈ H, (MulAut.conj c) v ∈ (P : Subgroup G) := by
  classical
  have hTp : IsPGroup p (Subgroup.zpowers v : Subgroup G) :=
    IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hvk)
  have hcop : ¬ p ∣ (P : Subgroup G).relIndex H := fun h =>
    P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPH))
  obtain ⟨c, hcH, hcP⟩ :=
    Work.NPC.Frobenius.exists_conj_le_of_relIndex_coprime hPH (Subgroup.zpowers_le.mpr hv)
      P.isPGroup' hTp hcop
  exact ⟨c, hcH, hcP (Subgroup.mem_map.mpr ⟨v, Subgroup.mem_zpowers v, rfl⟩)⟩

/-- Hall's fusion statement (M. Hall, §14.4): a `p`-element of `P` has the same `θ`-value as any
`G`-conjugate that lands in `H`.  Proof: by the diagonal computation for `p`-elements of `H`
(`prod_diagFactor_eq_of_pow_eq_one`, from `prod_diagFactor_eq` plus `theta_diagFactor_conj` and Sylow
conjugacy in `H`), `θ (g⁻¹*u*g) = θ (d(g⁻¹*u*g))`, and `d` is conjugation invariant, so this equals
`θ (d u) = θ u`. -/
theorem theta_conj_eq {G : Type*} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {H : Subgroup G} (hPH : (P : Subgroup G) ≤ H) (hz : Work.Grun.HallHyp p (P : Subgroup G) H)
    {A : Type*} [CommGroup A] (θ : H →* A) (hexp : ∀ a : A, a ^ p = 1)
    (u : (P : Subgroup G)) (g : G) (hg : g⁻¹ * (u : G) * g ∈ H) :
    θ ⟨g⁻¹ * (u : G) * g, hg⟩ = θ ⟨(u : G), hPH u.2⟩ := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  -- `u` is a `p`-element, hence so is its conjugate `v = g⁻¹ * u * g ∈ H`.
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp P.isPGroup' :
    ∀ y : (P : Subgroup G), ∃ k, y ^ p ^ k = 1) u
  have hkG : (u : G) ^ (p ^ k) = 1 := by
    simpa using congrArg (fun y : (P : Subgroup G) => (y : G)) hk
  have hvk : (g⁻¹ * (u : G) * g) ^ (p ^ k) = 1 := by
    rw [show g⁻¹ * (u : G) * g = (MulAut.conj g⁻¹) (u : G) by
          rw [MulAut.conj_apply]; group]
    rw [← map_pow, hkG, map_one]
  -- conjugate `v` into `P` by an element `c ∈ H`
  obtain ⟨c, hcH, hcP⟩ := exists_conj_mem_of_pow_eq_one hPH hg k hvk
  have hwH : (MulAut.conj c) (g⁻¹ * (u : G) * g) ∈ H := hPH hcP
  -- `θ` is invariant under conjugation by `c ∈ H`
  have e0 : θ ⟨g⁻¹ * (u : G) * g, hg⟩
      = θ ⟨(MulAut.conj c) (g⁻¹ * (u : G) * g), hwH⟩ := by
    have hc : (⟨(MulAut.conj c) (g⁻¹ * (u : G) * g), hwH⟩ : H)
        = (⟨c, hcH⟩ : H) * ⟨g⁻¹ * (u : G) * g, hg⟩ * (⟨c, hcH⟩ : H)⁻¹ :=
      Subtype.ext (by simp [MulAut.conj_apply])
    rw [hc, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  -- the diagonal contribution of the conjugate is `θ` of it (Aux 2) …
  have e1 : θ ⟨(MulAut.conj c) (g⁻¹ * (u : G) * g), hwH⟩
      = diagProd θ ((MulAut.conj c) (g⁻¹ * (u : G) * g)) :=
    (prod_diagFactor_eq hPH hz θ hexp ⟨(MulAut.conj c) (g⁻¹ * (u : G) * g), hcP⟩).symm
  -- … and the diagonal contribution is conjugation invariant (Hall 14.4.2)
  have e2 : diagProd θ ((MulAut.conj c) (g⁻¹ * (u : G) * g))
      = diagProd θ (g⁻¹ * (u : G) * g) := by
    have h := theta_diagFactor_conj θ (g⁻¹ * (u : G) * g) c⁻¹
    simpa [MulAut.conj_apply, inv_inv] using h
  have e3 : diagProd θ (g⁻¹ * (u : G) * g) = diagProd θ (u : G) :=
    theta_diagFactor_conj θ (u : G) g
  have e4 : diagProd θ (u : G) = θ ⟨(u : G), hPH u.2⟩ :=
    prod_diagFactor_eq hPH hz θ hexp u
  calc θ ⟨g⁻¹ * (u : G) * g, hg⟩
      = θ ⟨(MulAut.conj c) (g⁻¹ * (u : G) * g), hwH⟩ := e0
    _ = diagProd θ ((MulAut.conj c) (g⁻¹ * (u : G) * g)) := e1
    _ = diagProd θ (g⁻¹ * (u : G) * g) := e2
    _ = diagProd θ (u : G) := e3
    _ = θ ⟨(u : G), hPH u.2⟩ := e4

end Work.Grun
