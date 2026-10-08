import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer
import Submission.Work.AUTL2.Elementary
import Submission.Work.AUTL2.Galois.decomposition
import Submission.Work.AUTL2.Norm.square
import Submission.Work.AUTL2.Norm.fourgroup
import Submission.Work.AUTL2.A5.basic
import Submission.Work.AUTL2.A5.tools
import Submission.Work.AUTL2.A5.mat
import Submission.Work.AUTL2.A5.noInvol
import Submission.Work.AUTL2.A5.kleinExtend
import Submission.Work.AUTL2.Aut.pglIndex
import Submission.Work.AUTL2.Helper.not_elementaryAbelian_card_eight_of_dihOrCycSylow
import Submission.Work.AUTL2.Helper.mul_mem_iff_not_mem_of_relIndex_eq_two
import Submission.Work.AUTL2.Helper.not_dihOrCycSylow_of_mem_galHom
import Submission.Work.AUTL2.Helper.exists_involution_outside_of_sub_of_dihOrCycSylow

set_option maxHeartbeats 1600000

namespace Work.AUTL2.Main

open Work.AUTL2

/-- If `H` has even relative index in `Q` then there is `g ∈ Q \ H` with `g ^ 2 ∈ H`. -/
theorem exists_mem_notMem_sq_mem_of_even_relIndex {G : Type*} [Group G] [Finite G]
    (H Q : Subgroup G) (h : Even (H.relIndex Q)) :
    ∃ g ∈ Q, g ∉ H ∧ g ^ 2 ∈ H := by
  have hK : Even (H.subgroupOf Q).index := h
  obtain ⟨g₀, h1, h2⟩ := A5.exists_sq_mem_of_even_index (H.subgroupOf Q) hK
  refine ⟨(g₀ : G), g₀.2, fun hc => h1 ?_, ?_⟩
  · rwa [Subgroup.mem_subgroupOf]
  · have hh := h2
    rw [Subgroup.mem_subgroupOf] at hh
    simpa using hh

theorem a5odd (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    [DecidableEq (GaloisField p k)] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (Q : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hQ : Q ≤ Work.AUTL2.pgammaL (GaloisField p k))
    (hpsl : Work.AUTL2.pslImage (GaloisField p k) ≤ Q)
    (hdih : Work.GW2.DihOrCycSylow ↥Q) :
    Odd ((Q ⊓ Work.AUTL2.pglImage (GaloisField p k)).relIndex Q) := by
  classical
  set L : Subgroup (Equiv.Perm (P1 (GaloisField p k))) := pslImage (GaloisField p k) with hL
  set Pg : Subgroup (Equiv.Perm (P1 (GaloisField p k))) := pglImage (GaloisField p k) with hPg
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨g, hgQ, hgM, hg2M⟩ := exists_mem_notMem_sq_mem_of_even_relIndex (Q ⊓ Pg) Q hodd
  obtain ⟨x, hxP, τ, hτG, hgxτ⟩ := (Galois.decomposition (GaloisField p k)).1 g (hQ hgQ)
  have hMleQ : Q ⊓ Pg ≤ Q := inf_le_left
  have hMlePg : Q ⊓ Pg ≤ Pg := inf_le_right
  have hLM : L ≤ Q ⊓ Pg := fun l hl => ⟨hpsl hl, pslImage_le_pglImage (GaloisField p k) hl⟩
  have hgg : g * g ∈ Q ⊓ Pg := by simpa [pow_two] using hg2M
  -- `τ` is not trivial and `τ ^ 2 = 1`
  have hτne : τ ≠ 1 := by
    intro h
    apply hgM
    have hxQ : x ∈ Q := by rw [hgxτ, h, mul_one] at hgQ; exact hgQ
    rw [hgxτ, h, mul_one]
    exact ⟨hxQ, hxP⟩
  have hconjP : τ * x * τ⁻¹ ∈ Pg :=
    (Subgroup.le_normalizer_iff.mp (Galois.galSub_le_normalizer_pglImage (GaloisField p k)))
      τ hτG x hxP
  have hτ2 : τ * τ = 1 := by
    have hmem : τ * τ ∈ Pg := by
      have key : τ * τ = (x * (τ * x * τ⁻¹))⁻¹ * (g * g) := by rw [hgxτ]; group
      rw [key]
      exact mul_mem (inv_mem (mul_mem hxP hconjP)) (hMlePg hgg)
    have hall : τ * τ ∈ Pg ⊓ galSub (GaloisField p k) := ⟨hmem, mul_mem hτG hτG⟩
    rw [hPg, Galois.pglImage_inf_galSub, Subgroup.mem_bot] at hall
    exact hall
  obtain ⟨σ, hσeq⟩ := MonoidHom.mem_range.mp hτG
  have hσ2 : σ * σ = 1 := by
    apply Galois.galHom_injective (GaloisField p k)
    rw [map_mul, hσeq, hτ2, map_one]
  have hσne : σ ≠ 1 := by
    intro h
    exact hτne (by rw [← hσeq, h, map_one])
  -- if `τ ∈ Q` we are done: `Q` would contain an elementary abelian group of order `8`
  have hcontras : τ ∈ Q → False := fun hτQ =>
    Helper.not_dihOrCycSylow_of_mem_galHom p k hp hq Q hpsl σ hσ2 hσne
      (by rwa [hσeq]) hdih
  by_cases hxL : x ∈ L
  · -- Case A: `x ∈ pslImage`, so `τ = x⁻¹ g ∈ Q`
    exact hcontras (by
      have hxQ : x ∈ Q := hpsl hxL
      have hkey : x⁻¹ * g = τ := by rw [hgxτ]; group
      rw [← hkey]
      exact mul_mem (inv_mem hxQ) hgQ)
  · by_cases hPL : Pg ≤ Q
    · -- Case B1: `pglImage ≤ Q`, so `x ∈ Q` and again `τ ∈ Q`
      exact hcontras (by
        have hxQ : x ∈ Q := hPL hxP
        have hkey : x⁻¹ * g = τ := by rw [hgxτ]; group
        rw [← hkey]
        exact mul_mem (inv_mem hxQ) hgQ)
    · -- Case B2: `Q ⊓ Pg = L`, and no involution lies in `Q \ L`
      have hMLe : Q ⊓ Pg ≤ L := by
        by_contra hnot
        obtain ⟨m, hmM, hmL⟩ := Set.not_subset.mp hnot
        have hmPg : m ∈ Pg := hMlePg hmM
        have hmQ : m ∈ Q := hMleQ hmM
        have hPgQ : Pg ≤ Q := by
          intro pp hpp
          by_cases hppL : pp ∈ L
          · exact hpsl hppL
          · have hidx2 : L.relIndex Pg = 2 := Aut.pglIndex p k hp hq
            have hpm : pp * m ∈ L :=
              (Helper.mul_mem_iff_not_mem_of_relIndex_eq_two hidx2 hmPg hmL pp hpp).mpr hppL
            have hpp_eq : pp = (pp * m) * m⁻¹ := by group
            rw [hpp_eq]
            exact mul_mem (hpsl hpm) (inv_mem hmQ)
        exact hPL hPgQ
      have hML : Q ⊓ Pg = L := le_antisymm hMLe hLM
      have hEvenL : Even (L.relIndex Q) := by rwa [hML] at hodd
      obtain ⟨V, hVcard, hVL, hVsqV, -⟩ := Norm.fourgroup p k hp hq σ hσ2 hσne
      have hVsq1 : ∀ v ∈ V, v * v = 1 := fun v hv => by simpa [pow_two] using hVsqV v hv
      obtain ⟨z, hzQ, hzL, hzsq⟩ := Helper.exists_involution_outside_of_sub_of_dihOrCycSylow
        (GaloisField p k) Q hpsl hdih V hVL hVcard hVsq1 hEvenL
      -- decompose `z` in `PΓL = PGL · PΣL`
      obtain ⟨y, hyP, ρ, hρG, hzyρ⟩ :=
        (Galois.decomposition (GaloisField p k)).1 z (hQ hzQ)
      obtain ⟨ρ₀, hρ₀eq⟩ := MonoidHom.mem_range.mp hρG
      have hρne : ρ ≠ 1 := by
        intro h
        apply hzL
        have hyQ : y ∈ Q := by
          rw [hzyρ, h, mul_one] at hzQ
          exact hzQ
        have hyM : y ∈ Q ⊓ Pg := ⟨hyQ, hyP⟩
        have hyL : y ∈ L := by rwa [hML] at hyM
        rw [hzyρ, h, mul_one]
        exact hyL
      have hconjPz : ρ * y * ρ⁻¹ ∈ Pg :=
        (Subgroup.le_normalizer_iff.mp (Galois.galSub_le_normalizer_pglImage (GaloisField p k)))
          ρ hρG y hyP
      have hzz : z * z ∈ Pg := by rw [hzsq]; exact Pg.one_mem
      have hρ2 : ρ * ρ = 1 := by
        have hmem : ρ * ρ ∈ Pg := by
          have key : ρ * ρ = (y * (ρ * y * ρ⁻¹))⁻¹ * (z * z) := by rw [hzyρ]; group
          rw [key]
          exact mul_mem (inv_mem (mul_mem hyP hconjPz)) hzz
        have hall : ρ * ρ ∈ Pg ⊓ galSub (GaloisField p k) := ⟨hmem, mul_mem hρG hρG⟩
        rw [hPg, Galois.pglImage_inf_galSub, Subgroup.mem_bot] at hall
        exact hall
      -- the order-two field automorphism is unique: `ρ₀ = σ`
      have hρ₀2 : ρ₀ * ρ₀ = 1 := by
        apply Galois.galHom_injective (GaloisField p k)
        rw [map_mul, hρ₀eq, hρ2, map_one]
      have hρ₀ne : ρ₀ ≠ 1 := by
        intro h
        exact hρne (by rw [← hρ₀eq, h, map_one])
      have hρ₀eqσ : ρ₀ = σ := by
        obtain ⟨i, h2i, hσi⟩ := A5.sigma_pow_repr p k hp hq σ hσ2 hσne
        obtain ⟨j, h2j, hρj⟩ := A5.sigma_pow_repr p k hp hq ρ₀ hρ₀2 hρ₀ne
        have hij : i = j := by omega
        ext xx
        rw [hρj xx, hσi xx, hij]
      rw [← hρ₀eq, hρ₀eqσ] at hzyρ
      -- `z * g⁻¹ = y * x⁻¹ ∈ PGL ∩ Q = L`
      have hzgL : z * g⁻¹ ∈ L := by
        have h1 : z * g⁻¹ = y * x⁻¹ := by rw [hzyρ, hgxτ, ← hσeq]; group
        have hMmem : y * x⁻¹ ∈ Q ⊓ Pg := by
          refine ⟨?_, ?_⟩
          · rw [← h1]
            exact Q.mul_mem hzQ (Q.inv_mem hgQ)
          · exact Pg.mul_mem hyP (Pg.inv_mem hxP)
        have hLmem : y * x⁻¹ ∈ L := by rwa [hML] at hMmem
        rw [h1]
        exact hLmem
      -- hence `z ∈ (x * galHom σ) * L`, contradicting `coset_sq_ne_one`
      refine A5.coset_sq_ne_one p k hp hq σ hσ2 hσne x hxP hxL
        (g⁻¹ * (z * g⁻¹) * g) ?_ ?_
      · have hmem : g⁻¹ * (z * g⁻¹) * (g⁻¹)⁻¹ ∈ pslImage (GaloisField p k) :=
          (Subgroup.le_normalizer_iff.mp (Galois.pgammaL_le_normalizer_pslImage (GaloisField p k)))
            g⁻¹ (inv_mem (hQ hgQ)) (z * g⁻¹) hzgL
        rwa [inv_inv] at hmem
      · have hz_eq : z = x * galHom (GaloisField p k) σ * (g⁻¹ * (z * g⁻¹) * g) := by
          rw [hzyρ, hgxτ, ← hσeq]; group
        rw [← hz_eq, pow_two, hzsq]

end Work.AUTL2.Main
