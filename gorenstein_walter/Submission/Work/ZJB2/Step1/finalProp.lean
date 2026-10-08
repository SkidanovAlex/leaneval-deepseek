import Mathlib
import Submission.Work.ZJB.Step1.Defs
import Submission.Work.ZJB.ThompsonWeakClosed
import Submission.Work.ZJB2.Step1.zsLeZJProp
import Submission.Work.ZJB2.Step1.normJLeNormZJProp

/-!
# ZJB2, step (I), leaf I.8: the closing argument (Glauberman 1968, p. 1118 foot – p. 1119)

**I.8.**  Let `S`, `T` be Sylow `p`-subgroups of `G`, `n ∈ N_G(Z(J(T)))` with `Z(S)^n = Z(S)^a`,
and `Z(S)^a ≤ N_G(Z(J(S)))`.  If `N_G(Z(S))` satisfies `(C_p*)` (`CpStarIn p (normalizer (ZS S))`),
then `Z(S)^a ≤ Z(J(S))`.

The proof is the paper's, with conjugation written as `X^g = g⁻¹Xg` (so that, in Mathlib's
notation, `X^g = Work.ZJB.pconj X g = X.map (MulAut.conj g)`):

* take `b` with `T = b·S·b⁻¹` (equivalently `b⁻¹ T b = S`) and `c ∈ C_G(Z(S))` with
  `c·J(T)·c⁻¹ ≤ S` — Sylow conjugacy of the `p`-subgroups `J(T)` and `S` inside `C_G(Z(S))`
  (here `S` is Sylow in `C_G(Z(S))` because `Z(S) ≤ S`, i.e. `S ≤ C_G(Z(S))`).
  Then `(c b)·J(S)·(c b)⁻¹ = c·J(T)·c⁻¹ ≤ S`, so `c b` normalises `J(S)` by weak closure of
  `J(S)` in `S` (`Work.ZJB.thompsonJ_map_conj_eq_of_le`), hence
  `c b ∈ N_G(J(S)) ≤ N_G(Z(J(S)))` (`Work.ZJB2.Step1.normJLeNormZJProp`);
* `Y := c·Z(S)^a·c⁻¹` satisfies `Y ≤ Z(J(S))`: an element `x = c·u·c⁻¹` of `Y` has
  `u ∈ Z(S)^a = Z(S)^n`, i.e. `n·u·n⁻¹ ∈ Z(S) ≤ Z(J(T))`, and `n` normalises `Z(J(T))`; hence
  `u ∈ Z(J(T))`, and `Z(J(T)) = b·Z(J(S))·b⁻¹`; thus `x = (c b)·z·(c b)⁻¹` with `z ∈ Z(J(S))`,
  which lies in `Z(J(S))` because `c b` normalises it;
* also `Y^c = Z(S)^a ≤ N_G(Z(J(S)))` and `Y ≤ Z(J(S)) ≤ N_G(Z(J(S)))`, `Y` is a `p`-group and
  `c ∈ N_G(Z(S))`: `(C_p*)` in `M = N_G(Z(S))` (with Sylow subgroup `S`) gives `c = d·m` with
  `d ∈ C_M(Y)`, `m ∈ N_M(Z(J(S)))`; hence `Z(S)^a = Y^c = Y^m ≤ Z(J(S))`.
-/

namespace Work.ZJB2.Step1

open Work.ZJB

variable {G : Type*} [Group G]

/-- `X^g = X` for `g ∈ N_G(X)`, in the paper's convention `X^g = g⁻¹Xg`. -/
theorem pconj_eq_self_of_mem_normalizer {X : Subgroup G} {g : G}
    (h : g ∈ Subgroup.normalizer (X : Set G)) : Work.ZJB.pconj X g = X := by
  ext x
  rw [Work.ZJB.mem_pconj]
  exact (Subgroup.mem_normalizer_iff.mp h x).symm

theorem finalProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.FinalProp p G := by
  intro S T a n hCp hZJT hn hna hAN
  set SZ : Subgroup G := (S : Subgroup G) with hSZ
  set TZ : Subgroup G := (T : Subgroup G) with hTZ
  set Z : Subgroup G := Work.ZJB.ZS SZ with hZ
  set A : Subgroup G := Work.ZJB.pconj Z a with hA
  -- `A = Z^n`
  have hAn : A = Work.ZJB.pconj Z n := hna.symm
  have hZleCen : Z ≤ Subgroup.centralizer (SZ : Set G) := hZ.le.trans inf_le_left
  -- `S ≤ C_G(Z)`: elements of `S` commute with `Z = Z(S)`
  have hSZleCenZ : SZ ≤ Subgroup.centralizer (Z : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZleCen hz) s hs).symm
  -- and `J(T) ≤ C_G(Z)`, since `Z ≤ Z(J(T))`
  have hJTleCenZ : Work.GW2.thompsonJ TZ ≤ Subgroup.centralizer (Z : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ Work.GW2.thompsonJ TZ ⊓
        Subgroup.centralizer (Work.GW2.thompsonJ TZ : Set G) := hZJT hz
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz').2 x hx).symm
  -- `b` with `S^b = T`
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq G S T
  have hbT : TZ = SZ.map (MulAut.conj b).toMonoidHom := by
    have h := congrArg (fun P : Sylow p G => (P : Subgroup G)) hb
    simp only [Sylow.coe_subgroup_smul] at h
    rw [Subgroup.pointwise_smul_def] at h
    exact h.symm
  have hbJ : Work.GW2.thompsonJ TZ
      = (Work.GW2.thompsonJ SZ).map (MulAut.conj b).toMonoidHom := by
    rw [hbT, Work.GW2.thompsonJ_map_conj]
  have hbZJ : Work.GW2.ZJ TZ = (Work.GW2.ZJ SZ).map (MulAut.conj b).toMonoidHom := by
    rw [hbT]
    exact Work.ZJB.ZJ_map_conj SZ b
  -- `c ∈ C_G(Z)` with `J(T)^c ≤ S` (Sylow conjugacy inside `C_G(Z)`)
  obtain ⟨m, hmCen, hm⟩ := Work.ZJB.exists_mem_normalizer_inv_mul_mem (p := p) S hSZleCenZ hJTleCenZ
    (T.isPGroup'.to_le (Work.GW2.thompsonJ_le TZ))
  set c : G := m⁻¹ with hc
  have hcCen : c ∈ Subgroup.centralizer (Z : Set G) := Subgroup.inv_mem _ hmCen
  have hJc : (Work.GW2.thompsonJ TZ).map (MulAut.conj c).toMonoidHom ≤ SZ := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    have hv' : m⁻¹ * v * m ∈ SZ := hm v hv
    simpa [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hv'
  -- weak closure: `cb` normalises `J(S)`
  have hcbConj : (Work.GW2.thompsonJ SZ).map (MulAut.conj (c * b)).toMonoidHom ≤ SZ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyb : b * y * b⁻¹ ∈ Work.GW2.thompsonJ TZ := by
      rw [hbJ]
      exact Subgroup.mem_map.mpr ⟨y, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hcy : (MulAut.conj c).toMonoidHom (b * y * b⁻¹) ∈ SZ :=
      hJc (Subgroup.mem_map.mpr ⟨b * y * b⁻¹, hyb, rfl⟩)
    have heq : (MulAut.conj (c * b)).toMonoidHom y
        = (MulAut.conj c).toMonoidHom (b * y * b⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [heq]
    exact hcy
  have hcbNorm : c * b ∈ Subgroup.normalizer (Work.GW2.ZJ SZ : Set G) := by
    have h1 : c * b ∈ Subgroup.normalizer (Work.GW2.thompsonJ SZ : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact Work.ZJB.thompsonJ_map_conj_eq_of_le SZ (c * b) hcbConj
    exact (Work.ZJB2.Step1.normJLeNormZJProp (G := G) SZ) h1
  -- `Y := (Z^a)^c = (Z^n)^c`
  set Y : Subgroup G := A.map (MulAut.conj c).toMonoidHom with hY
  have hpcYc : Work.ZJB.pconj Y c = A := by
    ext x
    rw [Work.ZJB.mem_pconj]
    change c * x * c⁻¹ ∈ A.map (MulAut.conj c).toMonoidHom ↔ x ∈ A
    constructor
    · rintro ⟨u, hu, hux⟩
      have h1 : u = x := (MulAut.conj c).injective (by
        have h2 : (MulAut.conj c) u = c * x * c⁻¹ := hux
        have h3 : (MulAut.conj c) x = c * x * c⁻¹ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [h2, h3])
      rwa [h1] at hu
    · intro hx
      exact ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  -- `Y ≤ Z(J(S))`
  have hYle : Y ≤ Work.GW2.ZJ SZ := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx
    have hun : u ∈ Work.ZJB.pconj Z n := hAn ▸ hu
    have huJT : u ∈ Work.GW2.ZJ TZ := by
      have h1 : n * u * n⁻¹ ∈ Z := Work.ZJB.mem_pconj.mp hun
      have h2 : n * u * n⁻¹ ∈ Work.GW2.ZJ TZ := hZJT h1
      have h3 : u ∈ Work.ZJB.pconj (Work.GW2.ZJ TZ) n := Work.ZJB.mem_pconj.mpr h2
      rwa [pconj_eq_self_of_mem_normalizer hn] at h3
    rw [hbZJ] at huJT
    obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp huJT
    have hx' : x = (c * b) * z * (c * b)⁻¹ := by
      rw [← hux, ← hzu]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hx']
    exact (Subgroup.mem_normalizer_iff.mp hcbNorm z).mp hz
  have hYleSZ : Y ≤ SZ := hYle.trans (Work.GW2.ZJ_le SZ)
  have hYleZJnorm : Y ≤ Subgroup.normalizer (Work.GW2.ZJ SZ : Set G) :=
    hYleSZ.trans (Work.ZJB.le_normalizer_ZJ SZ)
  have hYleZnorm : Y ≤ Subgroup.normalizer (Z : Set G) :=
    (hYleSZ.trans hSZleCenZ).trans (Subgroup.centralizer_le_normalizer (Z : Set G))
  have hYp : IsPGroup p Y := S.isPGroup'.to_le hYleSZ
  -- `S` is a Sylow `p`-subgroup of `N_G(Z)`
  have hcNormZ : c ∈ Subgroup.normalizer (Z : Set G) :=
    Subgroup.centralizer_le_normalizer (Z : Set G) hcCen
  have hSylIn : Work.ZJB.IsSylowIn p SZ (Subgroup.normalizer (Z : Set G)) :=
    ⟨hSZleCenZ.trans (Subgroup.centralizer_le_normalizer (Z : Set G)), S.isPGroup',
      fun Q hSQ _ hQ => S.is_maximal' hQ hSQ⟩
  -- hypothesis of `(C_p*)` at `W = Y`, element `c`
  have hcond : ∀ w ∈ Y, c⁻¹ * w * c ∈ Subgroup.normalizer (Work.GW2.ZJ SZ : Set G) := by
    intro w hw
    obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.mp hw
    have heq : c⁻¹ * w * c = u := by
      rw [← huw]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [heq]
    exact hAN hu
  -- apply `(C_p*)` in `M = N_G(Z)`
  obtain ⟨d, mm, _hdM, hdC, _hmM, hmZJ, hcdm⟩ :=
    hCp SZ hSylIn Y hYleZnorm hYleZJnorm hYp c hcNormZ hcond
  -- `d ∈ C(Y)` acts trivially on `Y`
  have hdN : d ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.centralizer_le_normalizer (Y : Set G) hdC
  have hpcYm : Work.ZJB.pconj Y (d * mm) = Work.ZJB.pconj Y mm := by
    ext x
    rw [Work.ZJB.mem_pconj, Work.ZJB.mem_pconj]
    have heq : d * mm * x * (d * mm)⁻¹ = d * (mm * x * mm⁻¹) * d⁻¹ := by group
    constructor
    · intro hx
      rw [heq] at hx
      exact (Subgroup.mem_normalizer_iff.mp hdN (mm * x * mm⁻¹)).mpr hx
    · intro hx
      rw [heq]
      exact (Subgroup.mem_normalizer_iff.mp hdN (mm * x * mm⁻¹)).mp hx
  have hpcYmle : Work.ZJB.pconj Y mm ≤ Work.GW2.ZJ SZ := by
    intro x hx
    rw [Work.ZJB.mem_pconj] at hx
    exact (Subgroup.mem_normalizer_iff.mp hmZJ x).mpr (hYle hx)
  rw [← hpcYc, hcdm, hpcYm]
  exact hpcYmle

end Work.ZJB2.Step1
