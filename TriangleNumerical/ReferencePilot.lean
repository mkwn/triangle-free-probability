import TriangleNumerical.Statement
import TriangleNumerical.LogLadder

/-!
Root-free reference inequality (R0) of the blueprint, replayed with
kernel-checked rational arithmetic on top of the proved logarithm ladders.
The rational data below are untrusted witnesses produced by
`numerics/gen_reference_lean.py`; every inequality they are used in is proved
here from `TriangleLogCertificate`'s soundness theorems.
These local names do not change the frozen final target.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace TriangleReferencePilot
noncomputable section

open TriangleLogCertificate

def z (h : ℝ) : ℝ := Real.exp (-h)
def p (h : ℝ) : ℝ := 2 * h * z h / (1 - z h)^2
def t (h : ℝ) : ℝ := Real.exp (-p h)
def r (h : ℝ) : ℝ := t h * z h
def delta (h : ℝ) : ℝ := t h - r h
def alpha (h : ℝ) : ℝ := 2 * h / (3 * (delta h)^2)
def M2 (h : ℝ) : ℝ :=
  1 - (r h + t h) / 2 - alpha h * ((r h)^3 + 3 * r h * (t h)^2) / 2

/-! ### Rational witnesses -/

def zl : ℝ := (83555456237274533380843009 / 1000000000000000000000000000000 : ℝ)
def zu : ℝ := (41777728118720822146658863 / 500000000000000000000000000000 : ℝ)
def pl : ℝ := (12555469813449 / 8000000000000000 : ℝ)
def pu : ℝ := (784716863342133 / 500000000000000000 : ℝ)
def tl : ℝ := (199686357441215437 / 200000000000000000 : ℝ)
def tu : ℝ := (499215903587358133 / 500000000000000000 : ℝ)
def ruu : ℝ := (83424425170457 / 1000000000000000000 : ℝ)
def dl : ℝ := (124793545347613341 / 125000000000000000 : ℝ)
def au : ℝ := (6280729841099760779 / 1000000000000000000 : ℝ)
def m2l : ℝ := (499958897890904093 / 1000000000000000000 : ℝ)
def lxhi : ℝ := (-52608508336654447514992246784 / 39614081355123151658317745625 : ℝ)
def zLower : ℕ → ℝ
  | 0 => (1000000000000000000000000000000 / 83555456237274533380843009 : ℝ)
  | 1 => (2166866647486195763165177497721 / 19807040628566084398385987584 : ℝ)
  | 2 => (3314712540357252293703169854951 / 316912650057057350374175801344 : ℝ)
  | 3 => (4099706009639183844136670070467 / 1267650600228229401496703205376 : ℝ)
  | 4 => (1139845908870842795247052362061 / 633825300114114700748351602688 : ℝ)
  | 5 => (424989169060197277264563584027 / 316912650057057350374175801344 : ℝ)
  | 6 => (366993792607468886307451024525 / 316912650057057350374175801344 : ℝ)
  | 7 => (1364140610756665761465226304281 / 1267650600228229401496703205376 : ℝ)
  | 8 => (41094090588196369706471832115 / 39614081257132168796771975168 : ℝ)
  | 9 => (161389201311550520784378177675 / 158456325028528675187087900672 : ℝ)
  | 10 => (639664158622228208747646634627 / 633825300114114700748351602688 : ℝ)
  | 11 => (636738036645351088074533849009 / 633825300114114700748351602688 : ℝ)
  | 12 => (1270559998065123751062694387607 / 1267650600228229401496703205376 : ℝ)
  | 13 => (39659514544673538936770252933 / 39614081257132168796771975168 : ℝ)
  | 14 => (634188662259524193115150392715 / 633825300114114700748351602688 : ℝ)
  | 15 => (1268013910311100410477382370523 / 1267650600228229401496703205376 : ℝ)
  | 16 => (1267832242255895098847081730413 / 1267650600228229401496703205376 : ℝ)
  | 17 => (1267741417988852870877302350255 / 1267650600228229401496703205376 : ℝ)
  | 18 => (633848004147633961799209484707 / 633825300114114700748351602688 : ℝ)
  | 19 => (316918326014608500203916116119 / 316912650057057350374175801344 : ℝ)
  | 20 => (1267661952092503490892982684733 / 1267650600228229401496703205376 : ℝ)
  | 21 => (158457034518457431315602308331 / 158456325028528675187087900672 : ℝ)
  | 22 => (633826719092383842102599414603 / 633825300114114700748351602688 : ℝ)
  | 23 => (1267652019205704358288551788235 / 1267650600228229401496703205376 : ℝ)
  | 24 => (1267651309716768333863151489781 / 1267650600228229401496703205376 : ℝ)
  | 25 => (633825477486224615593224407025 / 633825300114114700748351602688 : ℝ)
  | 26 => (633825388800163453609971342217 / 633825300114114700748351602688 : ℝ)
  | 27 => (1267650688914275052078131652071 / 1267650600228229401496703205376 : ℝ)
  | 28 => (316912661142812862804349183831 / 316912650057057350374175801344 : ℝ)
  | _ => 1

def zUpper : ℕ → ℝ
  | 0 => (500000000000000000000000000000 / 41777728118720822146658863 : ℝ)
  | 1 => (17334933179872231172141538997827 / 158456325028528675187087900672 : ℝ)
  | 2 => (13258850161422379749731966539951 / 1267650600228229401496703205376 : ℝ)
  | 3 => (4099706009638158917634260397579 / 1267650600228229401496703205376 : ℝ)
  | 4 => (284961477217675078627110878729 / 158456325028528675187087900672 : ℝ)
  | 5 => (1699956676240682861765989289587 / 1267650600228229401496703205376 : ℝ)
  | 6 => (1467975170429829671005728164981 / 1267650600228229401496703205376 : ℝ)
  | 7 => (682070305378322223384091615721 / 633825300114114700748351602688 : ℝ)
  | 8 => (1315010898822273557084451578579 / 1267650600228229401496703205376 : ℝ)
  | 9 => (645556805246199561431242217717 / 633825300114114700748351602688 : ℝ)
  | 10 => (1279328317244453918807173651167 / 1267650600228229401496703205376 : ℝ)
  | 11 => (1273476073290700932520089875063 / 1267650600228229401496703205376 : ℝ)
  | 12 => (635279999032561565336035166185 / 633825300114114700748351602688 : ℝ)
  | 13 => (1269104465429552936136690713595 / 1267650600228229401496703205376 : ℝ)
  | 14 => (634188662259524115699542206739 / 633825300114114700748351602688 : ℝ)
  | 15 => (634006955155550166541977613757 / 633825300114114700748351602688 : ℝ)
  | 16 => (633916121127947530077956113989 / 633825300114114700748351602688 : ℝ)
  | 17 => (1267741417988852851533103467371 / 1267650600228229401496703205376 : ℝ)
  | 18 => (1267696008295267913926665976441 / 1267650600228229401496703205376 : ℝ)
  | 19 => (1267673304058433995979874577781 / 1267650600228229401496703205376 : ℝ)
  | 20 => (158457744011562936059388674193 / 158456325028528675187087900672 : ℝ)
  | 21 => (633828138073829724657943617029 / 633825300114114700748351602688 : ℝ)
  | 22 => (633826719092383841800367283079 / 633825300114114700748351602688 : ℝ)
  | 23 => (1267652019205704357986319995023 / 1267650600228229401496703205376 : ℝ)
  | 24 => (633825654858384166856017838877 / 633825300114114700748351602688 : ℝ)
  | 25 => (1267650954972449231110890929181 / 1267650600228229401496703205376 : ℝ)
  | 26 => (633825388800163453591081873643 / 633825300114114700748351602688 : ℝ)
  | 27 => (316912672228568763014810546205 / 316912650057057350374175801344 : ℝ)
  | 28 => (633825322285625725603976001015 / 633825300114114700748351602688 : ℝ)
  | _ => 1

def xLower : ℕ → ℝ
  | 0 => (200 / 53 : ℝ)
  | 1 => (2462502212820758688232001132635 / 1267650600228229401496703205376 : ℝ)
  | 2 => (1766802877557532689737083638729 / 1267650600228229401496703205376 : ℝ)
  | 3 => (748279481246941785332831346353 / 633825300114114700748351602688 : ℝ)
  | 4 => (688678783447389890803116443881 / 633825300114114700748351602688 : ℝ)
  | 5 => (660683007652509029655065898871 / 633825300114114700748351602688 : ℝ)
  | 6 => (323557415927083749472903010713 / 316912650057057350374175801344 : ℝ)
  | 7 => (1280871191819478133205272897741 / 1267650600228229401496703205376 : ℝ)
  | 8 => (637121875139484010157014577617 / 633825300114114700748351602688 : ℝ)
  | 9 => (635471449964159260580045811265 / 633825300114114700748351602688 : ℝ)
  | 10 => (634647841316335737626529272519 / 633825300114114700748351602688 : ℝ)
  | 11 => (9909944333922406358704469781 / 9903520314283042199192993792 : ℝ)
  | 12 => (39626927213583378344776482729 / 39614081257132168796771975168 : ℝ)
  | 13 => (1267856118871529713325481233243 / 1267650600228229401496703205376 : ℝ)
  | 14 => (1267753355385237387938306286781 / 1267650600228229401496703205376 : ℝ)
  | 15 => (633850988382807524100851905181 / 633825300114114700748351602688 : ℝ)
  | 16 => (316919072059161978128690097903 / 316912650057057350374175801344 : ℝ)
  | 17 => (1267663444167370738197244619111 / 1267650600228229401496703205376 : ℝ)
  | 18 => (1267657022181533172553511966585 / 1267650600228229401496703205376 : ℝ)
  | 19 => (79228363200050910812673682407 / 79228162514264337593543950336 : ℝ)
  | 20 => (79228262857094081876986602723 / 79228162514264337593543950336 : ℝ)
  | 21 => (39614106342831662081897147971 / 39614081257132168796771975168 : ℝ)
  | 22 => (1267651001599357751792941182375 / 1267650600228229401496703205376 : ℝ)
  | 23 => (1267650800913777691080895888029 / 1267650600228229401496703205376 : ℝ)
  | 24 => (633825350285499787449066165793 / 633825300114114700748351602688 : ℝ)
  | 25 => (1267650650399613495349790259867 / 1267650600228229401496703205376 : ℝ)
  | 26 => (1267650625313921200211344767363 / 1267650600228229401496703205376 : ℝ)
  | 27 => (1267650612771075238801049109041 / 1267650600228229401496703205376 : ℝ)
  | 28 => (19807040726557067259931758041 / 19807040628566084398385987584 : ℝ)
  | _ => 1

/-! ### Logarithm certificates -/

theorem log_zl : Real.log zl ≤ -(939 / 100) := by
  have hpos : ∀ i, i ≤ 28 → 1 ≤ zLower i := by
    intro i hi; interval_cases i <;> norm_num [zLower]
  have hstep : ∀ i, i < 28 → (zLower (i + 1)) ^ 2 ≤ zLower i := by
    intro i hi; interval_cases i <;> norm_num [zLower]
  have hlad := log_lower_ladder 28 zLower hpos hstep
  have hseed : (939 / 100 : ℝ) ≤ (2 : ℝ) ^ 28 * lowerSeed (zLower 28) := by
    norm_num [lowerSeed, zLower]
  have h0 : zLower 0 = 1 / zl := by norm_num [zLower, zl]
  rw [h0, one_div, Real.log_inv] at hlad
  linarith

theorem log_zu : -(939 / 100 : ℝ) ≤ Real.log zu := by
  have hpos : ∀ i, i ≤ 28 → 1 ≤ zUpper i := by
    intro i hi; interval_cases i <;> norm_num [zUpper]
  have hstep : ∀ i, i < 28 → zUpper i ≤ (zUpper (i + 1)) ^ 2 := by
    intro i hi; interval_cases i <;> norm_num [zUpper]
  have hlad := log_upper_ladder 28 zUpper hpos hstep
  have hseed : (2 : ℝ) ^ 28 * upperSeed (zUpper 28) ≤ (939 / 100 : ℝ) := by
    norm_num [upperSeed, zUpper]
  have h0 : zUpper 0 = 1 / zu := by norm_num [zUpper, zu]
  rw [h0, one_div, Real.log_inv] at hlad
  linarith

theorem log_x_upper : Real.log (53 / 200) ≤ lxhi := by
  have hpos : ∀ i, i ≤ 28 → 1 ≤ xLower i := by
    intro i hi; interval_cases i <;> norm_num [xLower]
  have hstep : ∀ i, i < 28 → (xLower (i + 1)) ^ 2 ≤ xLower i := by
    intro i hi; interval_cases i <;> norm_num [xLower]
  have hlad := log_lower_ladder 28 xLower hpos hstep
  have hseed : -((2 : ℝ) ^ 28 * lowerSeed (xLower 28)) ≤ lxhi := by
    norm_num [lowerSeed, xLower, lxhi]
  have h0 : xLower 0 = 1 / (53 / 200 : ℝ) := by norm_num [xLower]
  rw [h0, one_div, Real.log_inv] at hlad
  linarith

/-! ### Enclosures for the branch quantities at h = 9.39 -/

theorem z_lower : zl ≤ z (939 / 100) := by
  have h := exp_enclosure_of_log_bounds (-(939 / 100)) zl zu
    (by norm_num [zl]) (by norm_num [zu]) log_zl log_zu
  simpa [z] using h.1

theorem z_upper : z (939 / 100) ≤ zu := by
  have h := exp_enclosure_of_log_bounds (-(939 / 100)) zl zu
    (by norm_num [zl]) (by norm_num [zu]) log_zl log_zu
  simpa [z] using h.2

theorem z_lt_one : z (939 / 100) < 1 := by
  have hzu : zu < 1 := by norm_num [zu]
  exact lt_of_le_of_lt z_upper hzu

theorem p_lower : pl ≤ p (939 / 100) := by
  have h1 := z_lower
  have h2 := z_upper
  have h5 : 0 < 1 - z (939 / 100) := by linarith [z_lt_one]
  have hden : 0 < (1 - z (939 / 100)) ^ 2 := by positivity
  rw [p, le_div_iff₀ hden]
  have hzl : (0:ℝ) < zl := by norm_num [zl]
  have hA : (1 - z (939 / 100)) ^ 2 ≤ (1 - zl) ^ 2 := by nlinarith
  have hpl : (0:ℝ) < pl := by norm_num [pl]
  have hB : pl * (1 - z (939 / 100)) ^ 2 ≤ pl * (1 - zl) ^ 2 :=
    mul_le_mul_of_nonneg_left hA hpl.le
  have hC : pl * (1 - zl) ^ 2 ≤ 2 * (939 / 100 : ℝ) * zl := by norm_num [pl, zl]
  linarith

theorem p_upper : p (939 / 100) ≤ pu := by
  have h1 := z_lower
  have h2 := z_upper
  have h5 : 0 < 1 - z (939 / 100) := by linarith [z_lt_one]
  have hden : 0 < (1 - z (939 / 100)) ^ 2 := by positivity
  rw [p, div_le_iff₀ hden]
  have hzl : (0:ℝ) < zl := by norm_num [zl]
  have hzu1 : zu < 1 := by norm_num [zu]
  have hA : (1 - zu) ^ 2 ≤ (1 - z (939 / 100)) ^ 2 := by nlinarith
  have hpu : (0:ℝ) < pu := by norm_num [pu]
  have hB : pu * (1 - zu) ^ 2 ≤ pu * (1 - z (939 / 100)) ^ 2 :=
    mul_le_mul_of_nonneg_left hA hpu.le
  have hC : 2 * (939 / 100 : ℝ) * zu ≤ pu * (1 - zu) ^ 2 := by norm_num [pu, zu]
  nlinarith [h2]

theorem t_lower : tl ≤ t (939 / 100) := by
  have hseed : pu ≤ lowerSeed (1 / tl) := by norm_num [lowerSeed, tl, pu]
  have hlog : lowerSeed (1 / tl) ≤ Real.log (1 / tl) :=
    lower_seed_le_log _ (by norm_num [tl])
  have hli : Real.log (1 / tl) = -Real.log tl := by rw [one_div, Real.log_inv]
  rw [hli] at hlog
  have hlogtl : Real.log tl ≤ -pu := by linarith
  have h1 : tl ≤ Real.exp (-pu) := by
    calc tl = Real.exp (Real.log tl) := (Real.exp_log (by norm_num [tl])).symm
      _ ≤ Real.exp (-pu) := Real.exp_le_exp.2 hlogtl
  have h2 : Real.exp (-pu) ≤ Real.exp (-p (939 / 100)) :=
    Real.exp_le_exp.2 (by linarith [p_upper])
  simpa [t] using le_trans h1 h2

theorem t_upper : t (939 / 100) ≤ tu := by
  have hseed : upperSeed (1 / tu) ≤ pl := by norm_num [upperSeed, tu, pl]
  have hlog : Real.log (1 / tu) ≤ upperSeed (1 / tu) :=
    log_le_upper_seed _ (by norm_num [tu])
  have hli : Real.log (1 / tu) = -Real.log tu := by rw [one_div, Real.log_inv]
  rw [hli] at hlog
  have hlogtu : -pl ≤ Real.log tu := by linarith
  have h1 : Real.exp (-pl) ≤ tu := by
    calc Real.exp (-pl) ≤ Real.exp (Real.log tu) := Real.exp_le_exp.2 hlogtu
      _ = tu := Real.exp_log (by norm_num [tu])
  have h2 : Real.exp (-p (939 / 100)) ≤ Real.exp (-pl) :=
    Real.exp_le_exp.2 (by linarith [p_lower])
  simpa [t] using le_trans h2 h1

theorem r_upper : r (939 / 100) ≤ ruu := by
  have h1 := t_upper
  have h2 := z_upper
  have h3 : (0:ℝ) < t (939 / 100) := Real.exp_pos _
  have h4 : (0:ℝ) < z (939 / 100) := Real.exp_pos _
  have hkey : t (939 / 100) * z (939 / 100) ≤ tu * zu := by
    apply mul_le_mul h1 h2 h4.le
    norm_num [tu]
  have hnum : tu * zu ≤ ruu := by norm_num [tu, zu, ruu]
  simp only [r]
  linarith

theorem r_pos : 0 < r (939 / 100) := by
  have h3 : (0:ℝ) < t (939 / 100) := Real.exp_pos _
  have h4 : (0:ℝ) < z (939 / 100) := Real.exp_pos _
  simp only [r]
  positivity

theorem delta_lower : dl ≤ delta (939 / 100) := by
  have h1 := t_lower
  have h2 := r_upper
  have : dl ≤ tl - ruu := by norm_num [dl, tl, ruu]
  simp only [delta]
  linarith

theorem alpha_upper : alpha (939 / 100) ≤ au := by
  have h1 := delta_lower
  have hdl : (0:ℝ) < dl := by norm_num [dl]
  have hd : 0 < delta (939 / 100) := lt_of_lt_of_le hdl h1
  have hsq : dl ^ 2 ≤ (delta (939 / 100)) ^ 2 := by nlinarith
  rw [alpha, div_le_iff₀ (by positivity)]
  have hau : (0:ℝ) < au := by norm_num [au]
  have hnum : 2 * (939 / 100 : ℝ) ≤ au * (3 * dl ^ 2) := by norm_num [au, dl]
  nlinarith [mul_le_mul_of_nonneg_left hsq hau.le]

theorem alpha_pos : 0 < alpha (939 / 100) := by
  have hdl : (0:ℝ) < dl := by norm_num [dl]
  have hd : 0 < delta (939 / 100) := lt_of_lt_of_le hdl delta_lower
  rw [alpha]
  positivity

theorem M2_lower : m2l ≤ M2 (939 / 100) := by
  have hr := r_upper
  have hrp := r_pos
  have ht := t_upper
  have htp : (0:ℝ) < t (939 / 100) := Real.exp_pos _
  have ha := alpha_upper
  have hap := alpha_pos
  have hru : (0:ℝ) < ruu := by norm_num [ruu]
  have htu : (0:ℝ) < tu := by norm_num [tu]
  have ht2 : (t (939 / 100)) ^ 2 ≤ tu ^ 2 := by nlinarith
  have hc1 : (r (939 / 100)) ^ 3 ≤ ruu ^ 3 := pow_le_pow_left₀ hrp.le hr 3
  have hc2 : r (939 / 100) * (t (939 / 100)) ^ 2 ≤ ruu * tu ^ 2 :=
    mul_le_mul hr ht2 (by positivity) hru.le
  have hcube : (r (939 / 100)) ^ 3 + 3 * r (939 / 100) * (t (939 / 100)) ^ 2
      ≤ ruu ^ 3 + 3 * ruu * tu ^ 2 := by nlinarith [hc1, hc2]
  have hprod : alpha (939 / 100) *
      ((r (939 / 100)) ^ 3 + 3 * r (939 / 100) * (t (939 / 100)) ^ 2)
      ≤ au * (ruu ^ 3 + 3 * ruu * tu ^ 2) := by
    apply mul_le_mul ha hcube (by positivity) (by norm_num [au])
  have hfinal : m2l ≤ 1 - (ruu + tu) / 2 - au * (ruu ^ 3 + 3 * ruu * tu ^ 2) / 2 := by
    norm_num [m2l, ruu, tu, au]
  simp only [M2]
  linarith

/-! ### Lower enclosures and the coarse root bracket (blueprint 8.2) -/

/-! ### The reference comparison (R0) -/

theorem reference_trial_comparison :
    (3 / 1000000 : ℝ) <
      M2 (939 / 100) -
        (1 - (53 / 200 : ℝ) +
          (53 / 200 : ℝ) * Real.log (53 / 200 : ℝ) +
          alpha (939 / 100) * (53 / 200 : ℝ)^3) := by
  have h1 := M2_lower
  have h2 := log_x_upper
  have h3 := alpha_upper
  have hnum : (3 / 1000000 : ℝ) <
      m2l - (1 - (53 / 200 : ℝ) + (53 / 200 : ℝ) * lxhi + au * (53 / 200 : ℝ) ^ 3) := by
    norm_num [m2l, lxhi, au]
  nlinarith [h1, h2, h3]

end
end TriangleReferencePilot

#print axioms TriangleReferencePilot.reference_trial_comparison
