# 🛡️ DSA with SHA3 Signature Implementation 🚀

## Overview

This project demonstrates the implementation of the Digital Signature Algorithm (DSA) using the SHA3 hashing algorithm for secure and efficient message signing. The DSA algorithm provides a secure way to sign digital messages, ensuring data integrity and authenticity.

## Features

- **Secure Hashing:** Utilizes the SHA3 algorithm for secure and reliable message hashing.
- **Random Key Generation:** Generates random prime numbers for private key components to enhance security.
- **Key Pair Generation:** Creates public and private key pairs for the DSA algorithm.
- **Signing Algorithm:** Implements the DSA signing algorithm for generating digital signatures.
- **Verification Algorithm:** Provides a verification algorithm to validate the authenticity of digital signatures.

## How to Use

1. **Clone the Repository:**
   ```bash
   git clone https://github.com/snigdhab7/DSAwithSHA3.git
   ```

2. **Import Project:**
   - Import the project into your preferred C++ development environment.

3. **Build and Run:**
   - Build and run the `main.cpp` file to execute the DSA with SHA3 signature demonstration.

## Sample Run

```plaintext
---------------------------------------------SIGNING---------------------------------------------------

 H(m) for message (nkjdshfiueyew87r7436q0091274eiwjendkqwsadnxsakdjawiu64893264) : 49152196162199158251247411121813198198
 k :968294637493774585166872937050
 k inverse:1064476948539279090963356264888
Generated (r,s) pair : (695386754750856376345591505786 , 404235765735534794949256677587)
---------------------------------------------VERIFICATION---------------------------------------------------

 H(m) for message(nkjdshfiueyew87r7436q0091274eiwjendkqwsadnxsakdjawiu64893264) : 49152196162199158251247411121813198198
 v:695386754750856376345591505786

 SIGNATURE ACCEPTED!!
```
### Real-world example
```
________________________________________________________________________________________________________________________
p:41682761588380460785873834315179920031991877171793415143878006677653048780254651641566477787849507490526631561144542291525917719920848893213754238477905625799224211724721573332185160335043076449159921936835801768665600208147148908692 09077243730102315704405603706396632748991766437918740907923298627378264293342863321365545034743603, q : 1155813159887942210692943102459, 
g:37946097973305658833770862310873956194810072766172522259571173633463812123872689352630542378555865295340231186430108374627368809914889242542363338561074088085844121679923158264643095924092304978831111211259432066992413200230181453168 0535523908396017158493072002157596018956175624255808579021614059457102147014900018531742333252032, 
y:29427078328772413998804038667336394943863779861798011096290047376250980230495092816699035759418623765930025667579815946487168940160530273028469426335040918192928677182939788210486080554075935937375319338085812996279233720972720083564 98797424734822399941047122036521207265689140322235330283580695421630356443363230744361381087580448 
Private key x : 480 
enter message to be signed: nkjdshfiueyew87r7436q0091274eiwjendkqwsadnxsakdjawiu64893264 
SIGNING 
H(m) for message (nkjdshfiueyew87r7436q0091274eiwjendkqwsadnxsakdjawiu64893264) : 49152196162199158251247411121813198198 k :968294637493774585166872937050 k inverse:1064476948539279090963356264888 enerated (r,$) pair : (695386754750856376345591505786 , 404235765735534794949256677587) 
VERIFICATION 
H(m) for message(nkjdshfiueyew87r7436q0091274eiwjendkqwsadnxsakdjawiu64893264) : 49152196162199158251247411121813198198 v:695386754750856376345591505786

SIGNATURE ACCEPTED!! 
________________________________________________________________________________________________________________________

p:11015634817612814519778238207263632218732611593262484194930748656621249535442163102690188029725678773354124293124274838614058962286087052392785045821260389462691668106132735926971616442243004767822149551287215927062384785206911858925 595586452235934598504139664724197492395907130141813882308593446842948140401305269212751241302559243, 
q : 1133228327782330703275048025297, 
g:71613775681334540879203148660091547581969050841913543589338355025858095102291023143586112068292167772927347568555003355078652191982509604354778198329963674206354439527268432942970239710063071747706585581664318206469424443148587966904 43142891843926887071866509010104225108373637244445110506804674307856012261446747072153100447918389, 
y:58451814832100100332612052045757507825145924354765050230300275641269267408064677676702866054705624977981616607229209615883523314762877538212185088616303264101876561954390799840745569135110043551560183305051678286760634445909125374350 91160269815366758506803411939167353465452354484408298391167840531863930483992220175165394234751540 
Private key x : 198 
enter message to be signed: mdncksjdhfoisdjficdijcficn 
SIGNING 
H(m) for message (mdncksjdhfoisdjficdijcficn) : 10947212301981107318122065143196122122 k :244309481126254869140287083934 k inverse:788203817669864320039012320633 enerated (r,$) pair : (642652283287506210142687204121 , 543868153461933423671223743330) 
VERIFICATION 
H(m) for message(nksjfemcdoiere) : 13671821049117324225522522514984247247 v:890759475634171035829558262558

SIGNATURE REJECTED!! 
```
## Dependencies

- GMP Library: The project uses the GMP (GNU Multiple Precision Arithmetic Library) for handling large integers.


## Acknowledgments

- Special thanks to the creators of the GMP library for providing a robust platform for multiple precision arithmetic.

Feel free to explore, use, and contribute to this project!
